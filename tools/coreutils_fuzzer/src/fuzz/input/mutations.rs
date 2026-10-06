//! Shared whole-case and command-line mutation algorithms.
use super::system_state::{
    generate_fixture_blueprint, generate_missing_operands, random_file_contents,
};
use super::{
    accepts_mutation, generate_argv, generate_cwd, generate_system_state, generators, mutate_argv,
    normalize_case, regenerate_case_on_argv_mutation, support, utility_profile,
};
use crate::fuzz::{FixtureBlueprint, GeneratedCase};
use rand::prelude::SliceRandom;
use rand::rngs::StdRng;
use rand::Rng;

pub(crate) fn generate_case(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    max_fs_entries: usize,
) -> GeneratedCase {
    let profile = utility_profile(util);
    let mut fixture = generate_system_state(util, rng, max_fs_entries);
    let mut argv = generate_argv(util, &profile, option_pool, rng, max_args, &fixture);
    if super::requires_resolvable_fixture(util, &argv) {
        fixture = generate_fixture_blueprint(rng, max_fs_entries, false);
        argv = generate_argv(util, &profile, option_pool, rng, max_args, &fixture);
    }
    let stdin = if rng.random_bool(0.4) {
        random_file_contents(rng)
    } else {
        Vec::new()
    };
    let cwd = generate_cwd(util, rng, &fixture, false);
    let mut case = GeneratedCase {
        file_size_limit: None,
        argv,
        fixture,
        stdin,
        cwd,
    };
    normalize_case(util, &mut case);
    case
}

pub(crate) fn mutate_case_from_corpus(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    max_fs_entries: usize,
    base: &GeneratedCase,
) -> GeneratedCase {
    let mut case = base.clone();
    match rng.random_range(0..5) {
        0 if regenerate_case_on_argv_mutation(util) => {
            return generate_case(util, option_pool, rng, max_args, max_fs_entries)
        }
        0 => mutate_argv(
            util,
            option_pool,
            rng,
            max_args,
            &case.fixture,
            &mut case.argv,
        ),
        1 => mutate_stdin(rng, &mut case.stdin),
        2 => mutate_fixture_contents(rng, &mut case.fixture),
        3 => case.cwd = generate_cwd(util, rng, &case.fixture, true),
        _ => return generate_case(util, option_pool, rng, max_args, max_fs_entries),
    }
    normalize_case(util, &mut case);
    if !accepts_mutation(util, &case.argv) {
        return generate_case(util, option_pool, rng, max_args, max_fs_entries);
    }
    case
}

fn mutate_stdin(rng: &mut StdRng, stdin: &mut Vec<u8>) {
    if stdin.is_empty() || rng.random_bool(0.4) {
        *stdin = random_file_contents(rng);
    } else {
        stdin.truncate(stdin.len() / 2);
    }
}

fn mutate_fixture_contents(rng: &mut StdRng, fixture: &mut FixtureBlueprint) {
    if fixture.files.is_empty() {
        return;
    }
    let idx = rng.random_range(0..fixture.files.len());
    fixture.files[idx].bytes = random_file_contents(rng);
}

type OperandSource = fn(&FixtureBlueprint) -> Vec<String>;
type ReplacementGenerator = fn(&[String], usize, &mut StdRng) -> String;

pub(super) fn mutate_generic_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    if argv.is_empty() || rng.random_bool(0.35) {
        regenerate_argv(util, option_pool, rng, max_args, fixture, argv);
        return;
    }
    mutate_existing_argv(
        rng,
        max_args,
        fixture,
        argv,
        FixtureBlueprint::existing_operands,
        random_replacement_value,
    );
}

pub(in crate::fuzz::input) fn regenerate_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    *argv = generate_argv(
        util,
        &utility_profile(util),
        option_pool,
        rng,
        max_args,
        fixture,
    );
}

pub(in crate::fuzz::input) fn mutate_existing_argv(
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
    operand_source: OperandSource,
    replacement: ReplacementGenerator,
) {
    match rng.random_range(0..4) {
        0 if argv.len() > 1 => {
            let idx = rng.random_range(0..argv.len());
            argv.remove(idx);
        }
        1 if argv.len() < max_args.max(1) => {
            let operands = operand_source(fixture);
            argv.push(support::pick_target_operand(
                &operands,
                &generate_missing_operands(rng),
                rng,
                true,
            ));
        }
        2 => {
            let idx = rng.random_range(0..argv.len());
            argv[idx] = replacement(argv, idx, rng);
        }
        _ => argv.shuffle(rng),
    }
}

pub(in crate::fuzz::input) fn random_argument_value(rng: &mut StdRng) -> String {
    match rng.random_range(0..4) {
        0 => "-".to_string(),
        1 => format!("fuzz-name-{}", rng.random_range(0..1000)),
        2 => generators::chmod::random_chmod_mode(rng),
        _ => generators::touch::random_date_string(rng),
    }
}

pub(in crate::fuzz::input) fn random_non_stdin_argument_value(rng: &mut StdRng) -> String {
    match rng.random_range(0..3) {
        0 => format!("fuzz-name-{}", rng.random_range(0..1000)),
        1 => generators::chmod::random_chmod_mode(rng),
        _ => generators::touch::random_date_string(rng),
    }
}

fn random_replacement_value(_argv: &[String], _idx: usize, rng: &mut StdRng) -> String {
    random_argument_value(rng)
}

#[cfg(test)]
mod tests {
    use super::super::system_state::{
        contains_quote_trigger, generate_fixture_blueprint, random_file_contents,
        random_name_component, random_quote_trigger_component,
    };
    use super::super::{generate_system_state, generators::uniq::uniq_argv_is_supported};
    use super::{generate_case, mutate_case_from_corpus};
    use crate::fuzz::input::generators::ls::ls_argv_requires_followed_entry_metadata;
    use crate::fuzz::input::scenario_case;
    use crate::fuzz::system_state_concretizer::{stage_iteration_dirs, validate_fixture};
    use crate::fuzz::GeneratedCase;
    use crate::utils::arg_semantics::positional_args;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::PathBuf;

    fn materialized_fixture_has_dangling(
        root: &std::path::Path,
        iteration: usize,
        fixture: &crate::fuzz::FixtureBlueprint,
    ) -> bool {
        let (reference, _) = stage_iteration_dirs(root, None, iteration, fixture, false).unwrap();
        fixture
            .symlinks
            .iter()
            .any(|link| fs::metadata(reference.join(&link.relative_path)).is_err())
    }

    // Uniq support excludes a named output operand after the input operand.
    #[test]
    fn uniq_rejects_named_output_operand() {
        let argv = vec!["input".to_string(), "output".to_string()];

        assert!(!uniq_argv_is_supported(&argv));
    }

    // Uniq support permits standard output as the explicit output operand.
    #[test]
    fn uniq_accepts_standard_output_operand() {
        let argv = vec!["input".to_string(), "-".to_string()];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq support permits a single input operand.
    #[test]
    fn uniq_accepts_input_operand() {
        let argv = vec!["input".to_string()];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq support excludes a traditional skip-character operand.
    #[test]
    fn uniq_rejects_traditional_skip_operand() {
        let argv = vec!["+2000".to_string()];

        assert!(!uniq_argv_is_supported(&argv));
    }

    // Uniq support preserves the explicit extra-operand error path.
    #[test]
    fn uniq_accepts_three_operands() {
        let argv = vec![
            "input".to_string(),
            "output".to_string(),
            "extra".to_string(),
        ];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq help mode takes priority over a named output operand.
    #[test]
    fn uniq_accepts_help_with_named_output() {
        let argv = vec![
            "--help".to_string(),
            "input".to_string(),
            "output".to_string(),
        ];

        assert!(uniq_argv_is_supported(&argv));
    }

    // DU generation always supplies a regular-file domain and the modeled root cwd.
    #[test]
    fn du_generation_never_falls_back_to_default_directory() {
        let options = [
            "-b",
            "--bytes",
            "-A",
            "--apparent-size",
            "-B",
            "--block-size",
            "-s",
        ]
        .into_iter()
        .map(str::to_string)
        .collect::<Vec<_>>();
        for seed in 0..512 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = generate_case("du", &options, &mut rng, 10, 12);
            assert!(!case.fixture.files.is_empty(), "seed {seed}");
            assert_eq!(case.cwd, PathBuf::from("."), "seed {seed}");
            let files = case
                .fixture
                .files
                .iter()
                .map(|file| file.relative_path.to_string_lossy().into_owned())
                .collect::<BTreeSet<_>>();
            let operands = positional_args("du", &case.argv);
            assert!(
                operands.iter().all(|operand| files.contains(*operand)),
                "seed {seed}: {:?}",
                case.argv
            );
            assert_eq!(
                operands.iter().copied().collect::<BTreeSet<_>>().len(),
                operands.len(),
                "seed {seed}: {:?}",
                case.argv
            );
            assert!(
                crate::fuzz::input::generators::du::argv_stays_in_modeled_accounting_slice(
                    &case.argv,
                ),
                "seed {seed}: {:?}",
                case.argv
            );
        }
    }

    // Uniq treats a help token after the option terminator as a named output operand.
    #[test]
    fn uniq_rejects_help_operand_with_named_output() {
        let argv = vec!["--".to_string(), "--help".to_string(), "input".to_string()];

        assert!(!uniq_argv_is_supported(&argv));
    }

    // Uniq version mode takes priority over a traditional skip operand.
    #[test]
    fn uniq_accepts_version_with_traditional_skip_operand() {
        let argv = vec!["--version".to_string(), "+2000".to_string()];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Corpus mutation replaces a uniq case that gains a named output operand.
    #[test]
    fn uniq_corpus_mutation_stays_within_supported_operands() {
        let base = GeneratedCase {
            file_size_limit: None,
            argv: vec!["input".to_string()],
            fixture: generate_system_state("uniq", &mut StdRng::seed_from_u64(0), 4),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let mut rng = StdRng::seed_from_u64(118);
        let case = mutate_case_from_corpus("uniq", &[], &mut rng, 4, 4, &base);

        assert!(uniq_argv_is_supported(&case.argv), "{:?}", case.argv);
    }

    // Corpus mutation replaces every uniq case retaining a traditional skip operand.
    #[test]
    fn uniq_traditional_skip_corpus_mutation_stays_supported() {
        let base = GeneratedCase {
            file_size_limit: None,
            argv: vec!["+2000".to_string()],
            fixture: generate_system_state("uniq", &mut StdRng::seed_from_u64(0), 4),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        for seed in 0..1024 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = mutate_case_from_corpus("uniq", &[], &mut rng, 4, 4, &base);
            assert!(
                case.argv.iter().all(|arg| arg != "+2000") && uniq_argv_is_supported(&case.argv),
                "seed {seed}: {:?}",
                case.argv
            );
        }
    }

    // Metadata-producing -L cases receive a fixture whose symbolic-link targets all resolve.
    #[test]
    fn ls_followed_metadata_generation_uses_existing_symlink_targets() {
        let root = tempfile::tempdir().unwrap();
        let option_pool = ["-L", "-n", "-s", "-S", "-t", "-R"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let mut observed_followed_metadata = false;
        for seed in 0..256 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = generate_case("ls", &option_pool, &mut rng, 8, 8);
            if ls_argv_requires_followed_entry_metadata(&case.argv) {
                observed_followed_metadata = true;
                assert!(
                    !materialized_fixture_has_dangling(root.path(), seed as usize, &case.fixture),
                    "seed {seed}: {:?}",
                    case.argv
                );
            }
        }

        assert!(observed_followed_metadata);
    }

    // Name-only random ls generation retains dangling-link coverage outside the excluded slice.
    #[test]
    fn ls_name_only_generation_reaches_dangling_symlinks() {
        let root = tempfile::tempdir().unwrap();
        let reached = (0..256).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = generate_case("ls", &[], &mut rng, 8, 8);
            materialized_fixture_has_dangling(root.path(), seed as usize, &case.fixture)
        });

        assert!(reached);
    }

    // Corpus argv mutation never combines a known dangling fixture with metadata-producing -L.
    #[test]
    fn ls_dangling_corpus_mutation_stays_in_supported_slice() {
        let base = scenario_case("ls", 18).expect("name-only dangling ls scenario");
        let option_pool = ["-L", "-n", "-s", "-S", "-t", "-R"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        for seed in 0..1024 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = mutate_case_from_corpus("ls", &option_pool, &mut rng, 8, 8, &base);
            let retains_known_dangling = case.fixture.symlinks.iter().any(|link| {
                link.relative_path.as_path() == std::path::Path::new("dangling-link")
                    && link.target.as_path() == std::path::Path::new("missing-target")
            });
            assert!(
                !retains_known_dangling || !ls_argv_requires_followed_entry_metadata(&case.argv),
                "seed {seed}: {:?}",
                case.argv
            );
        }
    }

    // Random payloads cross a 4 KiB allocation boundary so block counts are not limited to 0 or 8.
    #[test]
    fn random_file_contents_reach_a_second_allocation_extent() {
        let reached = (0..512).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            random_file_contents(&mut rng).len() > 4096
        });

        assert!(reached);
    }

    // Random chmod fixtures reach nested directory trees.
    #[test]
    fn chmod_fixture_generation_reaches_nested_directories() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            generate_system_state("chmod", &mut rng, 12)
                .directories
                .iter()
                .any(|dir| dir.relative_path.components().count() > 1)
        });

        assert!(reached);
    }

    // Random chmod fixtures reach set-ID and sticky permission bits.
    #[test]
    fn chmod_fixture_generation_reaches_special_mode_bits() {
        let mut bits = 0;
        for seed in 0..1024 {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_system_state("chmod", &mut rng, 12);
            bits |= fixture
                .files
                .iter()
                .map(|file| file.mode)
                .chain(fixture.directories.iter().map(|dir| dir.mode))
                .fold(0, |seen, mode| seen | mode);
        }

        assert_eq!(bits & 0o7000, 0o7000);
    }

    // Random chmod fixtures reach symlinks whose target is a regular file.
    #[test]
    fn chmod_fixture_generation_reaches_file_symlink() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_system_state("chmod", &mut rng, 12);
            let files: BTreeSet<_> = fixture
                .files
                .iter()
                .map(|file| file.relative_path.as_path())
                .collect();
            fixture
                .symlinks
                .iter()
                .any(|link| files.contains(link.target.as_path()))
        });

        assert!(reached);
    }

    // Random chmod fixtures reach symlinks whose target is a directory.
    #[test]
    fn chmod_fixture_generation_reaches_directory_symlink() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_system_state("chmod", &mut rng, 12);
            let directories: BTreeSet<_> = fixture
                .directories
                .iter()
                .map(|dir| dir.relative_path.as_path())
                .collect();
            fixture
                .symlinks
                .iter()
                .any(|link| directories.contains(link.target.as_path()))
        });

        assert!(reached);
    }

    // Random chmod fixtures reach dangling symlink targets.
    #[test]
    fn chmod_fixture_generation_reaches_dangling_symlink() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_system_state("chmod", &mut rng, 12);
            let paths: BTreeSet<_> = fixture
                .files
                .iter()
                .map(|file| file.relative_path.as_path())
                .chain(
                    fixture
                        .directories
                        .iter()
                        .map(|dir| dir.relative_path.as_path()),
                )
                .chain(
                    fixture
                        .symlinks
                        .iter()
                        .map(|link| link.relative_path.as_path()),
                )
                .collect();
            fixture
                .symlinks
                .iter()
                .any(|link| !paths.contains(link.target.as_path()))
        });

        assert!(reached);
    }

    // Random chmod fixtures reach an explicit two-link cycle.
    #[test]
    fn chmod_fixture_generation_reaches_symlink_cycle() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_system_state("chmod", &mut rng, 12);
            fixture.symlinks.iter().any(|left| {
                fixture.symlinks.iter().any(|right| {
                    left.relative_path == right.target
                        && right.relative_path == left.target
                        && left.relative_path != right.relative_path
                })
            })
        });

        assert!(reached);
    }

    // Generated symlink hardlinks remain rooted when interpreted at every alias path.
    #[cfg(unix)]
    #[test]
    fn generated_symlink_hardlink_aliases_stay_within_fixture() {
        let mut symlink_hardlink_count = 0;
        for seed in 0..4096u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_fixture_blueprint(&mut rng, 12, true);

            validate_fixture(&fixture).unwrap_or_else(|error| {
                panic!("seed {seed} generated an invalid fixture: {error}")
            });
            symlink_hardlink_count += fixture
                .hardlinks
                .iter()
                .filter(|hardlink| {
                    fixture
                        .symlinks
                        .iter()
                        .any(|symlink| symlink.relative_path == hardlink.source_relative_path)
                })
                .count();
        }

        assert!(symlink_hardlink_count > 0);
    }

    // Generated trigger names stay legal POSIX filenames, or fixture staging breaks.
    #[test]
    fn quote_trigger_components_are_legal_filenames() {
        for seed in 0..256u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let name = random_quote_trigger_component(&mut rng, 3, 10);
            assert!(!name.is_empty());
            assert!(
                !name.contains('/'),
                "name must not contain a separator: {name:?}"
            );
            assert!(!name.contains('\0'), "name must not contain NUL: {name:?}");
            assert!(
                contains_quote_trigger(&name),
                "name must carry a trigger: {name:?}"
            );
        }
    }

    // The classifier's trigger test distinguishes triggering from plain operands.
    #[test]
    fn quote_trigger_detection_matches_operand_shape() {
        assert!(contains_quote_trigger("a'b"));
        assert!(contains_quote_trigger("next monday"));
        assert!(contains_quote_trigger("a\tb"));
        assert!(!contains_quote_trigger("plain-name_01.txt"));
    }

    // Ordinary generation still reaches plain names, so existing coverage survives.
    #[test]
    fn plain_name_components_are_still_generated() {
        let reached = (0..512u64).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let name = random_name_component(&mut rng, 4, 10);
            !contains_quote_trigger(&name)
        });
        assert!(reached);
    }
}
