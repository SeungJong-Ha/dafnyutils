use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::generic(scenario_case).with_case_normalizer(normalize_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = system_state::basic_fixture();
    Some(match iteration {
        0 => support::case(vec!["LC_ALL", "LANG"], fixture, b""),
        1 => support::case(vec!["LC_ALL", "MISSING", "LANG"], fixture, b""),
        2 => support::case(vec!["--null", "LC_ALL", "LANG"], fixture, b""),
        3 => support::case(vec!["-0", "LC_ALL", "LANG"], fixture, b""),
        4 => support::case(vec!["--", "-DASH"], fixture, b""),
        _ => return None,
    })
}

fn keep_printenv_on_explicit_variables(argv: &mut Vec<String>) {
    if printenv_has_explicit_variable(argv)
        || argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "--help" | "--version"))
    {
        return;
    }
    argv.push("LC_ALL".to_string());
    argv.push("LANG".to_string());
}

fn printenv_has_explicit_variable(argv: &[String]) -> bool {
    let mut after_options = false;
    for arg in argv {
        if after_options {
            return true;
        }
        match arg.as_str() {
            "-0" | "--null" => {}
            "--" => after_options = true,
            _ => return true,
        }
    }
    false
}

fn normalize_case(case: &mut GeneratedCase) {
    keep_printenv_on_explicit_variables(&mut case.argv);
}
