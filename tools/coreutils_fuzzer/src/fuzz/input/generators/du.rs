use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::system_state::{generate_fixture_blueprint, random_file_contents};
use super::super::{mutations, support, system_state, PatternInputGenerator};
use crate::fuzz::GeneratedCase;
use crate::fuzz::UtilityProfile;
use crate::fuzz::{FileSpec, FixtureBlueprint};
use crate::utils::arg_semantics::positional_args;
use rand::rngs::StdRng;
use std::path::PathBuf;

const SUMMARY: Element = Element::optional(35, Atom::Option(OptionChoice::available(&["-s"])));
const FILES: Element = Element::repeated(1, 3, Atom::Operand(OperandSource::ExistingFileUnique));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        1,
        &["--bytes"],
        &[Element::once(Atom::Literal("--bytes")), SUMMARY, FILES],
    ),
    Alternative::requiring(
        1,
        &["--apparent-size", "--block-size"],
        &[
            Element::once(Atom::Literal("--apparent-size")),
            Element::once(Atom::Literal("--block-size=1")),
            SUMMARY,
            FILES,
        ],
    ),
    Alternative::requiring(
        1,
        &["-b"],
        &[Element::once(Atom::Literal("-b")), SUMMARY, FILES],
    ),
    Alternative::weighted(2, &[Element::once(Atom::Literal("-b")), SUMMARY, FILES]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutations::regenerate_argv)
        .with_candidate_guard(argv_stays_in_modeled_accounting_slice)
        .with_system_state(generate_du_fixture_blueprint)
        .with_profile(UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        });

pub(crate) fn argv_stays_in_modeled_accounting_slice(argv: &[String]) -> bool {
    if argv
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "--version"))
    {
        return true;
    }
    let mut apparent = false;
    let mut block_size_one = false;
    let mut byte_counts = false;
    let mut index = 0;
    while index < argv.len() {
        let arg = &argv[index];
        if arg == "--" {
            break;
        }
        if matches!(arg.as_str(), "-b" | "--bytes") {
            byte_counts = true;
        }
        if matches!(arg.as_str(), "-A" | "--apparent-size") {
            apparent = true;
        }
        if arg == "-B" || arg == "--block-size" {
            block_size_one = argv.get(index + 1).is_some_and(|value| value == "1");
            index += 1;
        } else if let Some(value) = arg.strip_prefix("-B") {
            block_size_one = value == "1";
        } else if let Some(value) = arg.strip_prefix("--block-size=") {
            block_size_one = value == "1";
        }
        index += 1;
    }
    let operands = positional_args("du", argv);
    (byte_counts || apparent && block_size_one)
        && !operands.is_empty()
        && operands.iter().all(|operand| *operand != ".")
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = system_state::line_fixture();
    Some(match iteration {
        0 => support::case(vec!["-b", "a.txt"], fixture, b""),
        1 => support::case(vec!["--bytes", "empty.txt", "payload.bin"], fixture, b""),
        2 => support::case(
            vec!["--apparent-size", "--block-size=1", "payload.bin"],
            fixture,
            b"",
        ),
        3 => support::case(vec!["-b", "-s", "a.txt"], fixture, b""),
        4 => support::case(vec!["-b", "missing.txt"], fixture, b""),
        _ => return None,
    })
}

fn generate_du_fixture_blueprint(rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint {
    let mut fixture = generate_fixture_blueprint(rng, max_fs_entries.max(3), true);
    let mut suffix = 0;
    while fixture.files.len() < 3 {
        let relative_path = PathBuf::from(format!("du-input-{suffix}"));
        suffix += 1;
        let candidate = relative_path.to_string_lossy();
        if fixture
            .existing_operands()
            .iter()
            .any(|path| path == candidate.as_ref())
        {
            continue;
        }
        fixture.files.push(FileSpec {
            relative_path,
            bytes: random_file_contents(rng),
            mode: 0o644,
        });
    }
    fixture
}

#[cfg(test)]
mod tests {
    use super::argv_stays_in_modeled_accounting_slice;

    // DU shrinking may simplify operands but must retain byte accounting or an early request.
    #[test]
    fn modeled_accounting_predicate_covers_supported_spellings() {
        for argv in [
            vec!["-b", "file"],
            vec!["--bytes", "file"],
            vec!["-A", "-B1", "file"],
            vec!["--apparent-size", "--block-size", "1", "file"],
            vec!["--help"],
        ] {
            let argv = argv.into_iter().map(str::to_string).collect::<Vec<_>>();
            assert!(argv_stays_in_modeled_accounting_slice(&argv), "{argv:?}");
        }
        assert!(!argv_stays_in_modeled_accounting_slice(&[".".to_string()]));
        assert!(!argv_stays_in_modeled_accounting_slice(&[
            "-b".to_string(),
            ".".to_string(),
        ]));
        assert!(!argv_stays_in_modeled_accounting_slice(&["-b".to_string()]));
        assert!(!argv_stays_in_modeled_accounting_slice(&[
            "-A".to_string(),
            "-B1024".to_string(),
            "file".to_string(),
        ]));
    }
}
