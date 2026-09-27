use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::{FileSpec, GeneratedCase, HardlinkSpec, SymlinkSpec};
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::repeated(
        0,
        2,
        Atom::Option(OptionChoice::available(&["--help", "--version"])),
    ),
    Element::up_to_budget(
        0,
        Atom::Operand(OperandSource::Target {
            existing_percent: 70,
        }),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = fixtures::basic_fixture();
    let args = match iteration {
        0 => vec!["a.txt"],
        1 => vec!["a-link"],
        2 => {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("dangling"),
                target: PathBuf::from("missing.txt"),
            });
            vec!["dangling"]
        }
        3 => {
            fixture.hardlinks.push(HardlinkSpec {
                relative_path: PathBuf::from("alias"),
                source_relative_path: PathBuf::from("a.txt"),
            });
            vec!["alias"]
        }
        4 => vec![],
        5 => vec!["a.txt", "b.txt"],
        6 => vec!["missing.txt"],
        7 => vec![""],
        8 => vec!["dir"],
        9 => vec!["--help", "--version"],
        10 => vec!["--version", "--help"],
        11 => vec!["--help", "--bad"],
        12 => vec!["--bad", "--help"],
        13 => {
            fixture.files.push(FileSpec {
                relative_path: PathBuf::from("--help"),
                bytes: b"keep unless explicitly unlinked\n".to_vec(),
                mode: 0o644,
            });
            vec!["--", "--help"]
        }
        14 => vec!["--help=value"],
        15 => vec!["-x"],
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
