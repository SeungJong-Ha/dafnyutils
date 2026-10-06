use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, ValueSource};
use super::super::CwdPolicy;
use super::super::{mutations, support, PatternInputGenerator};
use crate::fuzz::UtilityProfile;
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase};
use rand::rngs::StdRng;
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::once(Atom::Operand(OperandSource::FileOrMissing {
        existing_percent: 85,
    })),
    Element::repeated(
        1,
        3,
        Atom::Value(ValueSource::Values(&["1", "2", "3", "4", "0"])),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutations::regenerate_argv)
        .with_system_state(random_system_state)
        .with_case_normalizer(normalize_case)
        .with_cwd_policy(CwdPolicy::Root)
        .with_profile(UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        });

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = generate_csplit_fixture_blueprint();
    Some(match iteration {
        0 => support::case(vec!["split.txt", "2"], fixture, b""),
        1 => support::case(vec!["-", "3"], fixture, b"red\nblue\ngreen\n"),
        2 => support::case(vec!["split.txt", "2", "4"], fixture, b""),
        3 => support::case(vec!["split.txt", "0"], fixture, b""),
        4 => {
            let mut case = support::case(vec!["split.txt", "2"], fixture, b"");
            case.file_size_limit = Some(2);
            case
        }
        _ => return None,
    })
}

fn generate_csplit_fixture_blueprint() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn random_system_state(_rng: &mut StdRng, _max_fs_entries: usize) -> FixtureBlueprint {
    generate_csplit_fixture_blueprint()
}

fn normalize_case(case: &mut GeneratedCase) {
    case.fixture = generate_csplit_fixture_blueprint();
    if case.argv.first().is_some_and(|arg| arg == "-") && case.stdin.is_empty() {
        case.stdin = b"alpha\nbeta\ngamma\n".to_vec();
    }
}
