use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::{DirSpec, FileSpec, GeneratedCase, HardlinkSpec, SymlinkSpec};
use std::path::PathBuf;

const HELP_OR_VERSION: Atom = Atom::Option(OptionChoice::available(&["--help", "--version"]));
const TARGET: Atom = Atom::Operand(OperandSource::Target {
    existing_percent: 70,
});

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::new(&[
        Element::repeated(0, 2, HELP_OR_VERSION),
        Element::up_to_budget(0, TARGET),
    ]),
    Alternative::new(&[
        Element::once(TARGET),
        Element::repeated(1, 2, HELP_OR_VERSION),
        Element::up_to_budget(0, TARGET),
    ]),
]);

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
        16 => vec!["--help", "a.txt"],
        17 => vec!["a.txt", "--help"],
        18 => vec!["a.txt", "--help", "b.txt"],
        19 => vec!["--version", "a.txt"],
        20 => vec!["a.txt", "--version"],
        21 => vec!["a.txt", "--version", "b.txt"],
        22 => vec!["--thisoptiondoesnotexist"],
        23 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            fixture.files.push(FileSpec {
                relative_path: PathBuf::from("blocked/target"),
                bytes: b"keep\n".to_vec(),
                mode: 0o644,
            });
            vec!["blocked/target"]
        }
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
