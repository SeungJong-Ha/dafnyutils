use super::*;
use crate::fuzz::comparison::compare::{compare_results_with_roots, render_text_diff};
use crate::fuzz::comparison::fs_snapshot::{
    restore_path_times, snapshot_fs, times_from_metadata, IdentityTransitionEvidence,
};
use crate::fuzz::comparison::CompareResult;
use crate::fuzz::coverage::extract_used_options;
use crate::fuzz::execution::run_variant;
use crate::fuzz::shrink::evaluate_case;
use crate::fuzz::shrink::reduce_fixture;
use crate::fuzz::system_state_concretizer::stage_iteration_dirs;
use crate::fuzz::{
    DirSpec, FileSpec, FixtureBlueprint, FsNodeSnapshot, FsSnapshot, FsTimes, GeneratedCase,
    HardlinkSpec, HostInodeKeySnapshot, ResolvedPaths, ResolvedTarget, RunResult, SymlinkSpec,
    VariantKind,
};
use clap::Parser;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
fn compare_results(
    util: &str,
    argv: &[String],
    reference: &RunResult,
    dut: &RunResult,
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    ignore_stderr: bool,
) -> CompareResult {
    compare_results_with_roots(
        util,
        argv,
        reference,
        dut,
        &IdentityTransitionEvidence::new(),
        reference_fs,
        &IdentityTransitionEvidence::new(),
        dut_fs,
        ignore_stderr,
        None,
        None,
        None,
    )
    .unwrap()
}

fn observed_process_outcome(code: i32) -> crate::fuzz::comparison::compare::ProcessOutcomeEvidence {
    crate::fuzz::comparison::compare::ProcessOutcomeEvidence::Observed(
        crate::fuzz::comparison::process_outcome::Termination::test_exit(code),
    )
}

mod argv;
mod fuzzer;
mod scenarios;
