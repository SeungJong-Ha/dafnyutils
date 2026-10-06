use super::comparison::compare::{
    compare_results_with_roots, fs_snapshots_match, mismatch_signature, replay_verdict_with_roots,
    MismatchSignature, ReplayVerdict,
};
use super::comparison::evaluation::{CaseVerdict, EvaluatedComparison};
use super::comparison::fs_snapshot::{
    snapshot_fs_post, snapshot_fs_pre_with_restore, snapshot_metadata_unchanged,
    IdentityTransitionEvidence,
};
use super::execution::{prepare_variant_with_limit, ExecutionEvidence};
use super::system_state_concretizer::{
    apply_fixture_modes, clone_fixture_tree, set_fixture_owner, stage_iteration_dirs,
};
use super::{FsSnapshot, GeneratedCase, ResolvedPaths, RunResult, VariantKind};
use crate::utils::arg_semantics::should_consume_stdin_from_argv;
use crate::utils::capabilities::{require_fuzz_capability, StdinDeliveryPolicy};
use crate::utils::cli::FuzzArgs;
use crate::utils::execution_context::selected_process_umask;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Debug, Clone)]
pub(crate) struct CaseEvaluation {
    pub(crate) case: GeneratedCase,
    pub(crate) reference: RunResult,
    pub(crate) dut: RunResult,
    pub(crate) comparison: EvaluatedComparison,
    pub(crate) mismatch_signature: Option<MismatchSignature>,
    pub(crate) replay_verdict: ReplayVerdict,
    pub(crate) pre_fs: FsSnapshot,
    pub(crate) dut_pre_fs: FsSnapshot,
    pub(crate) reference_fs: FsSnapshot,
    pub(crate) dut_fs: FsSnapshot,
    pub(crate) reference_identity: IdentityTransitionEvidence,
    pub(crate) dut_identity: IdentityTransitionEvidence,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RawCaseObservation {
    pub(crate) reference: RunResult,
    pub(crate) dut: RunResult,
    pub(crate) pre_fs: FsSnapshot,
    pub(crate) dut_pre_fs: FsSnapshot,
    pub(crate) reference_fs: FsSnapshot,
    pub(crate) dut_fs: FsSnapshot,
    pub(crate) reference_identity: IdentityTransitionEvidence,
    pub(crate) dut_identity: IdentityTransitionEvidence,
    pub(crate) execution: ExecutionEvidence,
    pub(crate) reference_root: PathBuf,
    pub(crate) dut_root: PathBuf,
}

pub(crate) trait CaseExecutor {
    fn execute(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String>;
}

#[cfg(test)]
struct LocalCaseExecutor<'a> {
    paths: &'a ResolvedPaths,
    work_root: &'a Path,
    shared_root: Option<&'a Path>,
}

#[cfg(test)]
impl CaseExecutor for LocalCaseExecutor<'_> {
    fn execute(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String> {
        execute_case_in_work_dir(
            args,
            self.paths,
            self.work_root,
            self.shared_root,
            seed,
            child_iteration,
            work_iteration,
            case,
            None,
        )
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn evaluate_case_with_seed(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    let mut executor = LocalCaseExecutor {
        paths,
        work_root,
        shared_root,
    };
    evaluate_case_with_executor(args, &mut executor, seed, iteration, iteration, case)
}

pub(crate) fn evaluate_case_with_executor(
    args: &FuzzArgs,
    executor: &mut dyn CaseExecutor,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    let observation = executor.execute(args, seed, child_iteration, work_iteration, case)?;
    finish_case_evaluation(args, case, observation)
}

#[cfg(test)]
pub(crate) fn evaluate_case(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    evaluate_case_with_seed(
        args,
        paths,
        work_root,
        shared_root,
        args.common.seed.unwrap_or_default(),
        iteration,
        case,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn execute_case_in_work_dir(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    case: &GeneratedCase,
    target_identity: Option<(u32, u32)>,
) -> Result<RawCaseObservation, String> {
    let process_timeout = Duration::from_secs(args.process_timeout_seconds);
    let controlled_fixture_times =
        require_fuzz_capability(&args.common.util)?.controlled_fixture_times;
    let (ref_dir, dut_dir) = stage_iteration_dirs(
        work_root,
        shared_root,
        work_iteration,
        &case.fixture,
        controlled_fixture_times,
    )?;
    let ref_dir = std::fs::canonicalize(&ref_dir)
        .map_err(|error| format!("resolve absolute fixture path: {error}"))?;
    let dut_dir = std::fs::canonicalize(&dut_dir)
        .map_err(|error| format!("resolve original fixture clone path: {error}"))?;
    if let Some((uid, gid)) = target_identity {
        set_fixture_owner(&ref_dir, uid, gid)?;
        set_fixture_owner(&dut_dir, uid, gid)?;
    }
    let umask = selected_process_umask(seed, child_iteration);
    if args.process_umask.is_some_and(|saved| saved != umask) {
        return Err(format!(
            "saved process umask differs from schedule: expected {umask:04o}"
        ));
    }
    let reference = prepare_variant_with_limit(
        VariantKind::Ref,
        paths,
        &case.argv,
        &case.cwd,
        &ref_dir,
        umask,
        target_identity,
        case.file_size_limit,
    )?;
    if let Some(saved) = &args.replay_fixture_times {
        super::system_state_concretizer::restore_fixture_time_inputs(&ref_dir, saved)?;
    }
    apply_fixture_modes(&ref_dir, &case.fixture)?;
    let (pre_fs, mut ref_observer) = snapshot_fs_pre_with_restore(&ref_dir, true)?;
    let stdin_delivery = require_fuzz_capability(&args.common.util)?.stdin_delivery;
    let process_stdin = if stdin_delivery == StdinDeliveryPolicy::Supplied
        || should_consume_stdin_from_argv(&args.common.util, &case.argv)
    {
        case.stdin.as_slice()
    } else {
        &[]
    };
    let (ref_result, reference_window) =
        reference.go_and_collect_timed(process_stdin, process_timeout)?;
    let (ref_fs, reference_identity) = snapshot_fs_post(&ref_dir, &mut ref_observer)?;
    let mut fixture_sharing = pre_fs == ref_fs && snapshot_metadata_unchanged(&ref_dir, &ref_fs)?;
    let mut prepared_dut = None;
    if fixture_sharing {
        prepared_dut = Some(prepare_variant_with_limit(
            VariantKind::Dut,
            paths,
            &case.argv,
            &case.cwd,
            &ref_dir,
            umask,
            target_identity,
            case.file_size_limit,
        )?);
        fixture_sharing = snapshot_metadata_unchanged(&ref_dir, &ref_fs)?;
    }
    let (dut, dut_pre_fs, mut dut_observer) = if fixture_sharing {
        (
            prepared_dut.take().expect("prepared shared DUT"),
            ref_fs.clone(),
            ref_observer,
        )
    } else {
        // Drop the waiting helper before replacing its cwd tree.
        drop(prepared_dut);
        clone_fixture_tree(&dut_dir, &ref_dir)?;
        let dut = prepare_variant_with_limit(
            VariantKind::Dut,
            paths,
            &case.argv,
            &case.cwd,
            &ref_dir,
            umask,
            target_identity,
            case.file_size_limit,
        )?;
        super::system_state_concretizer::restore_observed_fixture_times(&ref_dir, &pre_fs)?;
        apply_fixture_modes(&ref_dir, &case.fixture)?;
        let (pre, observer) = snapshot_fs_pre_with_restore(&ref_dir, true)?;
        if !fs_snapshots_match(&pre_fs, &pre, true)? {
            return Err("reference and DUT fixtures differ after pre-state observation".into());
        }
        (dut, pre, observer)
    };
    let (dut_result, dut_window) = dut.go_and_collect_timed(process_stdin, process_timeout)?;
    let (dut_fs, dut_identity) = snapshot_fs_post(&ref_dir, &mut dut_observer)?;
    let execution = ExecutionEvidence {
        fixture_sharing,
        reference_window,
        dut_window,
    };

    Ok(RawCaseObservation {
        reference: ref_result,
        dut: dut_result,
        pre_fs,
        dut_pre_fs,
        reference_fs: ref_fs,
        dut_fs,
        reference_identity,
        dut_identity,
        execution,
        reference_root: ref_dir.clone(),
        dut_root: ref_dir,
    })
}

fn finish_case_evaluation(
    args: &FuzzArgs,
    case: &GeneratedCase,
    observation: RawCaseObservation,
) -> Result<CaseEvaluation, String> {
    let RawCaseObservation {
        reference: ref_result,
        dut: dut_result,
        pre_fs,
        dut_pre_fs,
        reference_fs: ref_fs,
        dut_fs,
        reference_identity,
        dut_identity,
        reference_root: ref_dir,
        dut_root: dut_dir,
        execution,
    } = observation;
    let compare = compare_results_with_roots(
        &args.common.util,
        &case.argv,
        &ref_result,
        &dut_result,
        &reference_identity,
        &ref_fs,
        &dut_identity,
        &dut_fs,
        args.ignore_stderr,
        Some(ref_dir.as_path()),
        Some(dut_dir.as_path()),
        Some(case.cwd.as_path()),
    )?;
    let mismatch_signature = mismatch_signature(&compare, &reference_identity, &dut_identity);
    let mut replay_verdict = replay_verdict_with_roots(
        &args.common.util,
        &case.argv,
        &ref_result,
        &dut_result,
        &compare,
        &reference_identity,
        &dut_identity,
        &pre_fs,
        &dut_pre_fs,
        &ref_fs,
        &dut_fs,
        args.ignore_stderr,
        Some(ref_dir.as_path()),
        Some(dut_dir.as_path()),
        Some(case.cwd.as_path()),
    )?;
    replay_verdict.execution = Some(execution.clone());
    replay_verdict.validate_time_evidence()?;
    let mut evaluated = EvaluatedComparison::new(compare);
    evaluated.execution = Some(execution);
    Ok(CaseEvaluation {
        case: case.clone(),
        reference: ref_result,
        dut: dut_result,
        comparison: evaluated,
        mismatch_signature,
        replay_verdict,
        pre_fs,
        dut_pre_fs,
        reference_fs: ref_fs,
        dut_fs,
        reference_identity,
        dut_identity,
    })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn evaluate_case_in_work_dir(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    let observation = execute_case_in_work_dir(
        args,
        paths,
        work_root,
        shared_root,
        seed,
        child_iteration,
        work_iteration,
        case,
        None,
    )?;
    finish_case_evaluation(args, case, observation)
}

pub(crate) fn shrink_mismatch_with_executor(
    args: &FuzzArgs,
    executor: &mut dyn CaseExecutor,
    seed: u64,
    iteration: usize,
    original: CaseEvaluation,
    max_attempts: usize,
) -> Result<CaseEvaluation, String> {
    if max_attempts == 0 || original.comparison.verdict() != CaseVerdict::Mismatch {
        return Ok(original);
    }
    let Some(target_signature) = original.mismatch_signature else {
        return Ok(original);
    };

    let mut best = original;
    let mut attempts = 0usize;
    loop {
        let mut accepted = false;
        for candidate in reductions(&args.common.util, &best.case) {
            attempts += 1;
            if attempts > max_attempts {
                return Ok(best);
            }
            let work_iteration = iteration + 1_000_000 + attempts;
            let evaluation = evaluate_case_with_executor(
                args,
                executor,
                seed,
                iteration,
                work_iteration,
                &candidate,
            )?;
            if evaluation.comparison.verdict() == CaseVerdict::Mismatch
                && evaluation.mismatch_signature == Some(target_signature)
            {
                best = evaluation;
                accepted = true;
                break;
            }
        }
        if !accepted {
            break;
        }
    }
    Ok(best)
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn shrink_mismatch(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    iteration: usize,
    original: CaseEvaluation,
    max_attempts: usize,
) -> Result<CaseEvaluation, String> {
    let mut executor = LocalCaseExecutor {
        paths,
        work_root,
        shared_root,
    };
    shrink_mismatch_with_executor(args, &mut executor, seed, iteration, original, max_attempts)
}

fn reductions(util: &str, case: &GeneratedCase) -> Vec<GeneratedCase> {
    let mut out = Vec::new();
    out.extend(reduce_argv(util, case));
    if !super::input::requires_resolvable_fixture(util, &case.argv) {
        out.extend(reduce_fixture(case));
    }
    out.extend(reduce_contents(case));
    out.extend(reduce_stdin(case));
    out.extend(reduce_cwd(case));
    out
}

fn reduce_argv(util: &str, case: &GeneratedCase) -> Vec<GeneratedCase> {
    if case.argv.len() <= 1 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for idx in 0..case.argv.len() {
        let mut candidate = case.clone();
        candidate.argv.remove(idx);
        if candidate.argv != case.argv && super::input::accepts_candidate(util, &candidate.argv) {
            out.push(candidate);
        }
    }
    out
}

pub(crate) fn reduce_fixture(case: &GeneratedCase) -> Vec<GeneratedCase> {
    let mut out = Vec::new();
    if !case.fixture.hardlinks.is_empty() {
        let mut candidate = case.clone();
        candidate.fixture.hardlinks.pop();
        out.push(candidate);
    }
    if !case.fixture.symlinks.is_empty() {
        let mut candidate = case.clone();
        let removed = candidate
            .fixture
            .symlinks
            .pop()
            .expect("symlink is present");
        candidate
            .fixture
            .hardlinks
            .retain(|link| link.source_relative_path != removed.relative_path);
        out.push(candidate);
    }
    if case.fixture.files.len() > 1 {
        let mut candidate = case.clone();
        let removed = candidate.fixture.files.pop().expect("file is present");
        candidate
            .fixture
            .hardlinks
            .retain(|link| link.source_relative_path != removed.relative_path);
        out.push(candidate);
    }
    if case.fixture.directories.len() > 1 {
        if let Some(index) = case
            .fixture
            .directories
            .iter()
            .rposition(|directory| !case.cwd.starts_with(&directory.relative_path))
        {
            let mut candidate = case.clone();
            candidate.fixture.directories.remove(index);
            out.push(candidate);
        }
    }
    out
}

fn reduce_contents(case: &GeneratedCase) -> Vec<GeneratedCase> {
    let mut out = Vec::new();
    for idx in 0..case.fixture.files.len() {
        let bytes = &case.fixture.files[idx].bytes;
        if bytes.is_empty() {
            continue;
        }
        let mut candidate = case.clone();
        candidate.fixture.files[idx].bytes.truncate(bytes.len() / 2);
        out.push(candidate);
    }
    out
}

fn reduce_stdin(case: &GeneratedCase) -> Vec<GeneratedCase> {
    if case.stdin.is_empty() {
        return Vec::new();
    }
    let mut candidate = case.clone();
    candidate.stdin.truncate(case.stdin.len() / 2);
    vec![candidate]
}

fn reduce_cwd(case: &GeneratedCase) -> Vec<GeneratedCase> {
    if case.cwd.as_os_str().is_empty() || case.cwd == Path::new(".") {
        return Vec::new();
    }
    let mut candidate = case.clone();
    candidate.cwd = ".".into();
    vec![candidate]
}

#[cfg(test)]
mod tests {
    use super::{
        evaluate_case_in_work_dir, fs_snapshots_match, reduce_argv, reductions, shrink_mismatch,
        CaseEvaluation, IdentityTransitionEvidence, MismatchSignature,
    };
    use crate::fuzz::comparison::fs_snapshot::{snapshot_fs_post, snapshot_fs_pre_unrestored};
    use crate::fuzz::comparison::CompareResult;
    use crate::fuzz::execution::prepare_controlled_variant;
    use crate::fuzz::input::scenario_case;
    use crate::fuzz::system_state_concretizer::{apply_fixture_modes, stage_iteration_dirs};
    use crate::fuzz::{
        DirSpec, FileSpec, FixtureBlueprint, FsSnapshot, GeneratedCase, ResolvedPaths,
        ResolvedTarget, RunResult, SymlinkSpec, VariantKind,
    };
    use crate::utils::cli::{Cli, CliCommand, ExecKind};
    use crate::utils::execution_context::{canonical_environment_config, selected_process_umask};
    use clap::Parser;
    use std::path::PathBuf;

    // Both target executions receive the saved byte limit and retain the same failed-write prefix.
    #[cfg(target_os = "linux")]
    #[test]
    fn file_size_limit_is_shared_by_both_targets() {
        let root = tempfile::tempdir().unwrap();
        let CliCommand::Fuzz(args) = Cli::try_parse_from([
            "fuzzer",
            "fuzz",
            "--util",
            "tee",
            "--ref-kind",
            "native",
            "--dut-kind",
            "native",
        ])
        .unwrap()
        .command
        else {
            unreachable!()
        };
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/usr/bin/tee".into(),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/usr/bin/tee".into(),
                label: "dut",
            },
        };
        let case = scenario_case("tee", 11).unwrap();
        let observed = super::execute_case_in_work_dir(
            &args,
            &paths,
            root.path(),
            None,
            1,
            11,
            11,
            &case,
            None,
        )
        .unwrap();
        assert_eq!(observed.reference.termination.exit_code(), Some(1));
        assert_eq!(observed.dut.termination.exit_code(), Some(1));
        assert_eq!(observed.reference_fs["out"].data, case.stdin[..8]);
        assert_eq!(observed.dut_fs["out"].data, case.stdin[..8]);
        assert_eq!(observed.reference.stdout, case.stdin);
        assert_eq!(observed.dut.stdout, case.stdin);
    }

    // A saved case and its shrink candidates retain the execution condition that triggered failure.
    #[test]
    fn file_size_limit_survives_serialization_and_shrinking() {
        let case = scenario_case("tee", 11).unwrap();
        let encoded = serde_json::to_vec(&case).unwrap();
        let restored: GeneratedCase = serde_json::from_slice(&encoded).unwrap();
        assert_eq!(restored, case);
        let candidates = super::reduce_fixture(&case);
        assert!(!candidates.is_empty());
        assert!(candidates
            .iter()
            .all(|candidate| candidate.file_size_limit == Some(8)));
    }

    #[cfg(unix)]
    fn observe_script(script: &str) -> super::RawCaseObservation {
        observe_script_in_cwd(script, ".")
    }

    #[cfg(unix)]
    fn observe_script_in_cwd(script: &str, cwd: &str) -> super::RawCaseObservation {
        use std::os::unix::fs::PermissionsExt;
        let root = tempfile::tempdir().unwrap();
        let target = root.path().join("target");
        std::fs::write(&target, format!("#!/bin/sh\n{script}\n")).unwrap();
        std::fs::set_permissions(&target, std::fs::Permissions::from_mode(0o755)).unwrap();
        let CliCommand::Fuzz(args) =
            Cli::try_parse_from(["fuzzer", "fuzz", "--util", "cat", "--dut-kind", "native"])
                .unwrap()
                .command
        else {
            unreachable!()
        };
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: target.clone(),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: target,
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            stdin: Vec::new(),
            cwd: cwd.into(),
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: "work".into(),
                    mode: 0o755,
                }],
                hardlinks: Vec::new(),
                files: vec![FileSpec {
                    relative_path: "data".into(),
                    bytes: b"original".to_vec(),
                    mode: 0o644,
                }],
                symlinks: vec![
                    SymlinkSpec {
                        relative_path: "link".into(),
                        target: "data".into(),
                    },
                    SymlinkSpec {
                        relative_path: "cwd-link".into(),
                        target: "work".into(),
                    },
                ],
            },
        };
        super::execute_case_in_work_dir(&args, &paths, root.path(), None, 1, 0, 0, &case, None)
            .unwrap()
    }

    // Read-only pwd roles use exactly the same absolute cwd and reuse unchanged raw objects.
    #[cfg(unix)]
    #[test]
    fn read_only_roles_share_exact_fixture_and_absolute_path() {
        let observation = observe_script("/bin/pwd");
        assert_eq!(observation.reference_root, observation.dut_root);
        assert_eq!(observation.reference.stdout, observation.dut.stdout);
        assert_eq!(observation.pre_fs, observation.reference_fs);
        assert_eq!(observation.reference_fs, observation.dut_pre_fs);
        assert!(observation.execution.fixture_sharing);
        assert!(
            observation.execution.reference_window.end <= observation.execution.dut_window.start
        );
    }

    // Shrinking a formatted stat command must not switch to unsupported default output.
    #[test]
    fn stat_shrinking_preserves_required_format() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-c".into(), "%s".into(), "regular".into()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: ".".into(),
        };
        let candidates = super::reduce_argv("stat", &case);
        assert_eq!(candidates.len(), 2);
        assert!(candidates.iter().all(|candidate| candidate.argv[0] == "-c"));
    }

    // The same scope boundary still permits the real missing-format-value error case.
    #[test]
    fn stat_shrinking_keeps_missing_format_value_errors() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["--format".into(), "%s".into()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: ".".into(),
        };
        let candidates = super::reduce_argv("stat", &case);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].argv, ["--format"]);
    }

    // A mutating reference leaves preserved evidence while DUT receives original contents at the same path.
    #[cfg(unix)]
    #[test]
    fn mutating_roles_clone_original_fixture_at_same_path() {
        let observation =
            observe_script("/bin/pwd; /bin/cat data; sleep 0.02; printf mutated > data");
        assert_eq!(observation.reference_root, observation.dut_root);
        assert_eq!(observation.reference.stdout, observation.dut.stdout);
        assert!(!observation.execution.fixture_sharing);
        assert_eq!(observation.reference_fs["data"].data, b"mutated");
        assert_eq!(observation.dut_pre_fs["data"].data, b"original");
        assert_eq!(observation.dut_fs["data"].data, b"mutated");
        assert_ne!(
            observation.pre_fs["data"].host_key,
            observation.dut_pre_fs["data"].host_key
        );
    }

    // Following a symlink cwd during setup must preserve identical inputs on the fresh-clone branch.
    #[cfg(unix)]
    #[test]
    fn mutating_symlink_cwd_roles_preserve_identical_initial_times() {
        let observation = observe_script_in_cwd(
            "/bin/pwd; /bin/cat ../data; sleep 0.02; printf mutated > ../data",
            "cwd-link",
        );
        assert!(!observation.execution.fixture_sharing);
        assert_eq!(observation.reference.stdout, observation.dut.stdout);
        assert!(fs_snapshots_match(&observation.pre_fs, &observation.dut_pre_fs, true).unwrap());
        assert_eq!(
            observation.reference_fs["data"].data,
            observation.dut_fs["data"].data
        );
    }

    // Reducing a mismatch from a generated cwd must leave every candidate launchable there.
    #[test]
    fn fixture_reduction_preserves_generated_cwd() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["a".to_string(), "z".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![
                    DirSpec {
                        relative_path: "other".into(),
                        mode: 0o755,
                    },
                    DirSpec {
                        relative_path: "bw-1n".into(),
                        mode: 0o755,
                    },
                ],
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"a".to_vec(),
            cwd: "bw-1n".into(),
        };
        let candidates = super::reduce_fixture(&case);
        assert_eq!(candidates.len(), 1);
        for candidate in candidates {
            let root = tempfile::tempdir().unwrap();
            crate::fuzz::system_state_concretizer::materialize_fixture(
                root.path(),
                &candidate.fixture,
            )
            .unwrap();
            let output = std::process::Command::new("/bin/pwd")
                .current_dir(root.path().join(&candidate.cwd))
                .output()
                .unwrap();
            assert!(output.status.success());
        }
    }

    // An ancestor's removal must not invalidate a cwd selected beneath that directory.
    #[test]
    fn fixture_reduction_preserves_cwd_ancestors() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: vec![
                    DirSpec {
                        relative_path: "parent/child".into(),
                        mode: 0o755,
                    },
                    DirSpec {
                        relative_path: "parent".into(),
                        mode: 0o755,
                    },
                ],
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: "parent/child".into(),
        };
        assert!(super::reduce_fixture(&case).is_empty());
    }

    // ls 축소는 시각 선택자만 남겨 GNU의 암시 정렬 차이를 새 불일치로 만들지 않는다.
    #[test]
    fn ls_argv_shrink_preserves_time_selector_dependency() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-t".to_string(), "--time=status".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        let candidates = reduce_argv("ls", &case);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].argv, vec!["-t"]);
    }

    // DU shrinking must not replace an in-slice mismatch with unsupported accounting.
    #[test]
    fn du_argv_shrink_preserves_byte_accounting() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-b".to_string(), "-s".to_string(), ".".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        let candidates = reduce_argv("du", &case);

        assert!(candidates.iter().all(|candidate| {
            crate::fuzz::input::generators::du::argv_stays_in_modeled_accounting_slice(
                &candidate.argv,
            )
        }));
        assert!(!candidates
            .iter()
            .any(|candidate| candidate.argv == ["-s", "."]));
    }

    // Metadata-producing -L shrinking must not turn a valid implicit link into a dangling one.
    #[test]
    fn ls_followed_metadata_shrink_preserves_fixture_topology() {
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-L".to_string(), "-n".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: vec![FileSpec {
                    relative_path: PathBuf::from("target"),
                    bytes: b"payload".to_vec(),
                    mode: 0o644,
                }],
                symlinks: vec![SymlinkSpec {
                    relative_path: PathBuf::from("link"),
                    target: PathBuf::from("target"),
                }],
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        let candidates = reductions("ls", &case);

        assert!(candidates.iter().all(|candidate| {
            candidate.fixture.directories.len() == case.fixture.directories.len()
                && candidate.fixture.files.len() == case.fixture.files.len()
                && candidate.fixture.symlinks == case.fixture.symlinks
                && candidate.fixture.hardlinks == case.fixture.hardlinks
                && candidate.fixture.files[0].relative_path == case.fixture.files[0].relative_path
        }));
    }

    // A reduction evaluation failure must abort shrinking instead of being silently skipped.
    #[test]
    fn shrink_propagates_reduction_evaluation_error() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "true",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/definitely/missing/reference"),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/bin/true"),
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["first".to_string(), "second".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let identity = IdentityTransitionEvidence::new();
        let original = CaseEvaluation {
            case,
            reference: RunResult {
                termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
            dut: RunResult {
                termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
            comparison: super::EvaluatedComparison::new(CompareResult::Mismatch {
                process_outcome_diff: Some((
                    crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
                        crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
                    ),
                    crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
                        crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
                    ),
                )),
                stdout_diff: false,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }),
            mismatch_signature: Some(MismatchSignature::ProcessOutcome),
            replay_verdict: crate::fuzz::comparison::compare::ReplayVerdict {
                execution: None,
                comparison: CompareResult::Mismatch {
                    process_outcome_diff: Some((
                        crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
                            crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
                        ),
                        crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
                            crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
                        ),
                    )),
                    stdout_diff: false,
                    stderr_diff: false,
                    fs_diff: Vec::new(),
                },
                reference_process_outcome:
                    crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
                        crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
                    ),
                dut_process_outcome:
                    crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
                        crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
                    ),
                reference_stdout: crate::fuzz::comparison::compare::ReplayStreamEvidence::RawBytes(
                    Vec::new(),
                ),
                dut_stdout: crate::fuzz::comparison::compare::ReplayStreamEvidence::RawBytes(
                    Vec::new(),
                ),
                reference_stderr: crate::fuzz::comparison::compare::ReplayStreamEvidence::RawBytes(
                    Vec::new(),
                ),
                dut_stderr: crate::fuzz::comparison::compare::ReplayStreamEvidence::RawBytes(
                    Vec::new(),
                ),
                reference_identity: identity.clone(),
                dut_identity: identity.clone(),
                reference_pre_fs: crate::fuzz::comparison::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
                dut_pre_fs: crate::fuzz::comparison::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
                reference_post_fs: crate::fuzz::comparison::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
                dut_post_fs: crate::fuzz::comparison::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
            },
            pre_fs: FsSnapshot::new(),
            dut_pre_fs: FsSnapshot::new(),
            reference_fs: FsSnapshot::new(),
            dut_fs: FsSnapshot::new(),
            reference_identity: identity.clone(),
            dut_identity: identity,
        };
        let root = tempfile::tempdir().unwrap();

        let error =
            shrink_mismatch(&args, &paths, root.path(), None, 1, 0, original, 1).unwrap_err();

        assert!(error.contains("failed to run reference variant"), "{error}");
    }

    // Explicit chmod case stdin reaches both targets despite its semantic non-reading policy.
    #[cfg(unix)]
    #[test]
    fn explicit_chmod_case_preserves_supplied_stdin_delivery() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            unreachable!()
        };
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/bin/sh".into(),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/bin/sh".into(),
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-c".into(), "cat".into()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"explicit chmod input\n".to_vec(),
            cwd: ".".into(),
        };
        let root = tempfile::tempdir().unwrap();

        let observed =
            super::execute_case_in_work_dir(&args, &paths, root.path(), None, 1, 0, 0, &case, None)
                .unwrap();

        assert_eq!(observed.reference.stdout, case.stdin);
        assert_eq!(observed.reference.termination.exit_code(), Some(0));
        assert_eq!(observed.reference, observed.dut);
    }

    // Every registered utility creates files under the same seed/iteration umask schedule.
    #[cfg(unix)]
    #[test]
    fn every_utility_uses_the_scheduled_creation_mask() {
        let root = tempfile::tempdir().unwrap();
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/bin/sh".into(),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/bin/sh".into(),
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-c".into(), "umask; : > created".into()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: ".".into(),
        };
        for (utility_index, capability) in crate::utils::capabilities::UTILITY_CAPABILITIES
            .iter()
            .enumerate()
        {
            let cli = Cli::try_parse_from([
                "coreutils_fuzzer",
                "fuzz",
                "--util",
                capability.utility,
                "--dut-kind",
                "native",
            ])
            .unwrap();
            let CliCommand::Fuzz(args) = cli.command else {
                unreachable!()
            };
            for (iteration, mask) in [0o077, 0o000, 0o005, 0o022, 0o027].into_iter().enumerate() {
                let observed = super::execute_case_in_work_dir(
                    &args,
                    &paths,
                    root.path(),
                    None,
                    4,
                    iteration,
                    5 * utility_index + iteration,
                    &case,
                    None,
                )
                .unwrap();
                assert_eq!(
                    observed.reference.stdout,
                    format!("{mask:04o}\n").as_bytes(),
                    "{}",
                    capability.utility
                );
                assert_eq!(observed.reference, observed.dut);
                for fs in [&observed.reference_fs, &observed.dut_fs] {
                    assert_eq!(
                        fs["created"].mode_octal,
                        format!("{:04o}", 0o666 & !mask),
                        "{}",
                        capability.utility
                    );
                }
            }
        }
    }

    // A non-chmod utility enters a restrictive cwd at READY before final modes are observed.
    #[cfg(unix)]
    #[test]
    fn non_chmod_restrictive_cwd_is_finalized_before_prestate() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "cat",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            unreachable!()
        };
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/bin/cat".into(),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: "/bin/cat".into(),
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["--version".into()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: "d".into(),
                    mode: 0,
                }],
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: "d".into(),
        };
        let root = tempfile::tempdir().unwrap();

        let observed =
            super::execute_case_in_work_dir(&args, &paths, root.path(), None, 1, 0, 0, &case, None)
                .unwrap();

        assert_eq!(observed.reference.termination.exit_code(), Some(0));
        assert_eq!(observed.reference, observed.dut);
        assert!(!observed.reference.stdout.is_empty());
        use std::os::unix::fs::PermissionsExt;
        for directory in [&observed.reference_root, &observed.dut_root] {
            assert_eq!(
                std::fs::symlink_metadata(directory.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0
            );
        }
        for fs in [
            &observed.pre_fs,
            &observed.dut_pre_fs,
            &observed.reference_fs,
            &observed.dut_fs,
        ] {
            if fs["d"].kind == "inaccessible" {
                assert!(fs["d"].mode_octal.is_empty());
            } else {
                assert_eq!(fs["d"].mode_octal, "0000");
            }
        }
    }

    // Shrink work-directory numbering must not change the original seed/iteration umask schedule.
    #[cfg(unix)]
    #[test]
    fn chmod_shrink_preserves_original_child_configuration() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-c".to_string(), "umask".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 4, 3, 1_000_017, &case)
                .unwrap();

        assert_eq!(evaluation.reference.stdout, b"0022\n");
        assert_eq!(evaluation.reference, evaluation.dut);
    }

    // Pre-state observation must not give otherwise identical chmod roles different atimes.
    #[cfg(unix)]
    #[test]
    fn chmod_roles_start_from_identical_observed_filesystems() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/true"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = scenario_case("chmod", 0).unwrap();
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 0, 0, &case).unwrap();

        assert!(fs_snapshots_match(&evaluation.pre_fs, &evaluation.reference_fs, true).unwrap());
        assert!(fs_snapshots_match(&evaluation.reference_fs, &evaluation.dut_fs, true).unwrap());
        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::comparison::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::comparison::evaluation::CaseVerdict::Match
        );
    }

    // A declared mode-zero cwd must not prevent either chmod role from launching there.
    #[cfg(unix)]
    #[test]
    fn chmod_roles_launch_from_declared_unsearchable_cwd() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/chmod"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["--version".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: PathBuf::from("d"),
                    mode: 0o000,
                }],
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("d"),
        };
        let root = tempfile::tempdir().unwrap();
        let (ref_dir, dut_dir) =
            stage_iteration_dirs(root.path(), None, 597, &case.fixture, true).unwrap();
        let umask = selected_process_umask(1, 597);
        let environment = canonical_environment_config(umask).unwrap();
        let reference = prepare_controlled_variant(
            VariantKind::Ref,
            &paths,
            &case.argv,
            &case.cwd,
            &ref_dir,
            &environment,
            umask,
            None,
        )
        .unwrap();
        let dut = prepare_controlled_variant(
            VariantKind::Dut,
            &paths,
            &case.argv,
            &case.cwd,
            &dut_dir,
            &environment,
            umask,
            None,
        )
        .unwrap();

        apply_fixture_modes(&ref_dir, &case.fixture).unwrap();
        apply_fixture_modes(&dut_dir, &case.fixture).unwrap();
        for role_dir in [&ref_dir, &dut_dir] {
            assert_eq!(
                fs::symlink_metadata(role_dir.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }
        let (pre_fs, mut ref_observer) = snapshot_fs_pre_unrestored(&ref_dir).unwrap();
        let (dut_pre_fs, mut dut_observer) = snapshot_fs_pre_unrestored(&dut_dir).unwrap();
        assert!(fs_snapshots_match(&pre_fs, &dut_pre_fs, true).unwrap());

        let reference_result = reference
            .go_and_collect(&case.stdin, std::time::Duration::from_secs(10))
            .unwrap();
        let dut_result = dut
            .go_and_collect(&case.stdin, std::time::Duration::from_secs(10))
            .unwrap();
        assert_eq!(reference_result, dut_result);
        let (reference_fs, _) = snapshot_fs_post(&ref_dir, &mut ref_observer).unwrap();
        let (dut_fs, _) = snapshot_fs_post(&dut_dir, &mut dut_observer).unwrap();
        assert!(fs_snapshots_match(&reference_fs, &dut_fs, true).unwrap());
        for role_dir in [&ref_dir, &dut_dir] {
            assert_eq!(
                fs::symlink_metadata(role_dir.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 597, 1_000_597, &case)
                .unwrap();

        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::comparison::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::comparison::evaluation::CaseVerdict::Match
        );
        for snapshot in [
            &evaluation.pre_fs,
            &evaluation.reference_fs,
            &evaluation.dut_fs,
        ] {
            assert_eq!(snapshot["d"].kind, "inaccessible");
            assert!(snapshot["d"].mode_octal.is_empty());
        }
        {
            let role = "ref";
            assert_eq!(
                fs::symlink_metadata(root.path().join("iter-1000597").join(role).join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }
    }

    // Recursive chmod preserves controlled access/modification times without reversing change time.
    #[cfg(unix)]
    #[test]
    fn chmod_recursive_traversal_preserves_controlled_raw_times() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/chmod"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-R".to_string(), "0755".to_string(), "dir".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: PathBuf::from("dir"),
                    mode: 0o700,
                }],
                files: vec![FileSpec {
                    relative_path: PathBuf::from("dir/a.txt"),
                    bytes: b"alpha\n".to_vec(),
                    mode: 0o600,
                }],
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 7, 7, &case).unwrap();

        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::comparison::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::comparison::evaluation::CaseVerdict::Match
        );
        assert!(fs_snapshots_match(&evaluation.reference_fs, &evaluation.dut_fs, true).unwrap());
        assert_eq!(
            evaluation.reference_fs.keys().collect::<Vec<_>>(),
            evaluation.pre_fs.keys().collect::<Vec<_>>()
        );
        assert_eq!(evaluation.reference_fs["dir"].mode_octal, "0755");
        assert_eq!(evaluation.reference_fs["dir/a.txt"].data, b"alpha\n");
        let before = evaluation.pre_fs["dir"].times;
        let after = evaluation.reference_fs["dir"].times;
        assert_eq!(
            (after.atime_sec, after.atime_nsec),
            (before.atime_sec, before.atime_nsec)
        );
        assert_eq!(
            (after.mtime_sec, after.mtime_nsec),
            (before.mtime_sec, before.mtime_nsec)
        );
        assert!(
            (after.ctime_sec, after.ctime_nsec) >= (before.ctime_sec, before.ctime_nsec),
            "chmod must not move change time backward"
        );
    }

    // Newly visible chmod nodes expose the same controlled raw times from both fixture roles.
    #[cfg(unix)]
    #[test]
    fn chmod_newly_visible_nodes_reveal_controlled_fixture_times() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/chmod"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = scenario_case("chmod", 40).unwrap();
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 40, 40, &case).unwrap();

        assert_eq!(evaluation.pre_fs["d"].kind, "inaccessible");
        assert!(!evaluation.pre_fs.contains_key("d/e"));
        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::comparison::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::comparison::evaluation::CaseVerdict::Match
        );
        assert!(fs_snapshots_match(&evaluation.reference_fs, &evaluation.dut_fs, true).unwrap());
        assert_eq!(evaluation.reference_fs["d"].mode_octal, "0700");
        assert_eq!(evaluation.reference_fs["d/e"].mode_octal, "0700");
        for path in ["d", "d/e"] {
            let times = evaluation.reference_fs[path].times;
            assert_eq!(
                (times.atime_sec, times.atime_nsec),
                (
                    super::super::execution::CONTROLLED_FIXTURE_ATIME_SEC,
                    super::super::execution::CONTROLLED_FIXTURE_TIME_NSEC,
                )
            );
            assert_eq!(
                (times.mtime_sec, times.mtime_nsec),
                (
                    super::super::execution::CONTROLLED_FIXTURE_MTIME_SEC,
                    super::super::execution::CONTROLLED_FIXTURE_TIME_NSEC,
                )
            );
        }
    }
}
