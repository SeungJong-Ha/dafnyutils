use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = system_state::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"line\n"),
        1 => support::case(vec!["out"], fixture, b"line\n"),
        2 => support::case(vec!["-a", "target.txt"], fixture, b"line 2\n"),
        3 => support::case(vec!["one", "two", "three"], fixture, b"payload\n"),
        4 => support::case(vec!["dir/out"], fixture, b"nested\n"),
        5 => support::case(
            vec![""],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        6 => support::case(
            vec!["a.txt/"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        7 => support::case(
            vec!["a-link/"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        8 => support::case(
            vec!["dir"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        9 => support::case(
            vec!["missing/out"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        10 => support::case(
            vec!["loop"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        11 => {
            let mut case = support::case(
                vec!["out"],
                system_state::failure_fixture(),
                b"payload longer than limit\n",
            );
            case.file_size_limit = Some(8);
            case
        }
        12 => {
            let mut case = support::case(
                vec!["-a", "target.txt"],
                system_state::failure_fixture(),
                b"payload longer than limit\n",
            );
            case.file_size_limit = Some(8);
            case
        }
        _ => return None,
    })
}
