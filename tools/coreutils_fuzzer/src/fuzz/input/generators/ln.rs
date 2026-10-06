use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, ValueContext,
};
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::GeneratedCase;
use crate::fuzz::UtilityProfile;
use rand::rngs::StdRng;
use rand::Rng;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::once(Atom::Option(OptionChoice::with_fallback(
        &["-s", "--symbolic"],
        "-s",
    ))),
    Element::once(Atom::Operand(OperandSource::Generated(ln_source))),
    Element::once(Atom::Operand(OperandSource::Generated(ln_name))),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case).with_profile(UtilityProfile {
        requires_path_operand: true,
        prefers_existing_paths: true,
    });

fn ln_source(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    if rng.random_bool(0.2) {
        format!("missing-target-{}", rng.random_range(0..1000))
    } else {
        let files = support::existing_file_operands(context.fixture());
        support::pick_file_or_missing(&files, rng)
    }
}

fn ln_name(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let files = support::existing_file_operands(context.fixture());
    if rng.random_bool(0.2) && !files.is_empty() {
        support::pick_string(&files, rng)
    } else {
        format!("link-{}.sym", rng.random_range(0..10000))
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = system_state::line_fixture();
    Some(match iteration {
        0 => support::case(vec!["-s", "a.txt", "a.sym"], fixture, b""),
        1 => support::case(
            vec!["--symbolic", "missing-target", "dangling.sym"],
            fixture,
            b"",
        ),
        2 => support::case(vec!["-s", "a.txt", "target.txt"], fixture, b""),
        3 => support::case(vec!["-s"], fixture, b""),
        4 => support::case(
            vec!["a.txt/", ""],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        5 => support::case(
            vec!["missing", "new"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        6 => support::case(
            vec!["dir", "new"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        7 => support::case(
            vec!["a.txt", "target.txt"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        8 => support::case(
            vec!["a.txt", "missing/new"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        9 => support::case(
            vec!["a.txt", "new/"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        10 => support::case(
            vec!["dir-link/", "new"],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        11 => support::case(
            vec!["a.txt", ""],
            system_state::failure_fixture(),
            b"payload longer than limit\n",
        ),
        _ => return None,
    })
}
