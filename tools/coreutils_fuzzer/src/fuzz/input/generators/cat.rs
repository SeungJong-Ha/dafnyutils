use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::CwdPolicy;
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::GeneratedCase;
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::repeated(
        0,
        2,
        Atom::Option(OptionChoice::available(&[
            "-A",
            "--show-all",
            "-b",
            "--number-nonblank",
            "-E",
            "--show-ends",
            "-n",
            "--number",
            "-s",
            "--squeeze-blank",
            "-T",
            "--show-tabs",
            "-v",
            "--show-nonprinting",
        ])),
    ),
    Element::repeated(
        0,
        3,
        Atom::Operand(OperandSource::Stream {
            existing_weight: 3,
            missing_weight: 1,
            stdin_weight: 1,
            allow_repeated_stdin: true,
        }),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_cwd_policy(CwdPolicy::RootOnGeneration);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = system_state::basic_fixture();
    Some(match iteration {
        0 => GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture,
            stdin: b"stdin line\n".to_vec(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            file_size_limit: None,
            argv: vec!["a.txt".to_string(), "b.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            file_size_limit: None,
            argv: vec!["-".to_string(), "a.txt".to_string()],
            fixture,
            stdin: b"prefix\n".to_vec(),
            cwd: PathBuf::from("."),
        },
        3 => GeneratedCase {
            file_size_limit: None,
            argv: vec!["a.txt".to_string(), "missing.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        4 => support::case(
            vec!["a.txt/child"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        5 => support::case(
            vec!["a-link/"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        6 => support::case(
            vec!["loop"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        7 => support::case(
            vec!["dangling"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        8 => support::case(
            vec![""],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        9 => support::case(
            vec!["dir"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        _ => return None,
    })
}
