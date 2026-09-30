use super::{FixtureBlueprint, GeneratedCase, UtilityProfile};
use crate::utils::capabilities::capability_for;
use rand::rngs::StdRng;
use std::fmt::Debug;
use std::path::PathBuf;

pub(crate) mod generators;
pub(crate) mod mutations;
mod pattern;
mod support;
pub(crate) mod system_state;

type ScenarioFn = fn(usize) -> Option<GeneratedCase>;
type MutationFn = fn(&str, &[String], &mut StdRng, usize, &FixtureBlueprint, &mut Vec<String>);
type SystemStateFn = fn(&mut StdRng, usize) -> FixtureBlueprint;

/// Controls directory selection without changing the draws used by existing generators.
#[derive(Debug, Clone, Copy)]
enum CwdPolicy {
    Random,
    Root,
    RootOnGeneration,
}

impl CwdPolicy {
    fn generate(self, rng: &mut StdRng, fixture: &FixtureBlueprint, mutation: bool) -> PathBuf {
        match self {
            Self::Root => PathBuf::from("."),
            Self::RootOnGeneration if !mutation => PathBuf::from("."),
            _ => fixture.random_cwd(rng),
        }
    }
}

pub(crate) trait InputGenerator: Debug + Sync {
    /// Supplies path preferences to generic argument generation.
    fn profile(&self) -> UtilityProfile;

    /// Builds the filesystem input used by random case generation.
    fn generate_system_state(&self, rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint;

    /// Chooses the working directory for generation or corpus mutation.
    fn generate_cwd(&self, rng: &mut StdRng, fixture: &FixtureBlueprint, mutation: bool)
        -> PathBuf;

    /// Restores utility-specific relationships between arguments and supplied inputs.
    fn normalize_case(&self, case: &mut GeneratedCase);

    /// Reports whether changing arguments requires regenerating the whole case.
    fn regenerate_case_on_argv_mutation(&self) -> bool;

    /// Checks corpus mutation support independently from shrink candidate acceptance.
    fn accepts_mutation(&self, argv: &[String]) -> bool;

    fn generate_argv(
        &self,
        profile: &UtilityProfile,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
    ) -> Vec<String>;

    fn scenario_case(&self, iteration: usize) -> Option<GeneratedCase>;

    fn mutate_argv(
        &self,
        util: &str,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
        argv: &mut Vec<String>,
    );

    fn has_utility_pattern(&self) -> bool;

    /// Reports whether a shrink or mutation candidate argv stays inside the input slice the
    /// generator models.
    fn accepts_candidate(&self, _argv: &[String]) -> bool {
        true
    }

    /// Reports whether `argv` needs every fixture symbolic link to resolve.
    fn requires_resolvable_fixture(&self, _argv: &[String]) -> bool {
        false
    }
}

#[derive(Debug)]
pub(crate) struct PatternInputGenerator {
    argv_pattern: Option<&'static pattern::ArgvPattern>,
    scenario: ScenarioFn,
    mutation: MutationFn,
    candidate_guard: Option<fn(&[String]) -> bool>,
    resolvable_fixture: Option<fn(&[String]) -> bool>,
    profile: UtilityProfile,
    system_state: SystemStateFn,
    case_normalizer: Option<fn(&mut GeneratedCase)>,
    cwd_policy: CwdPolicy,
    regenerate_case_on_argv_mutation: bool,
    mutation_guard: Option<fn(&[String]) -> bool>,
}

impl PatternInputGenerator {
    const fn generic(scenario: ScenarioFn) -> Self {
        Self {
            argv_pattern: None,
            scenario,
            mutation: mutations::mutate_generic_argv,
            candidate_guard: None,
            resolvable_fixture: None,
            profile: UtilityProfile {
                requires_path_operand: false,
                prefers_existing_paths: false,
            },
            system_state: system_state::random_system_state,
            case_normalizer: None,
            cwd_policy: CwdPolicy::Random,
            regenerate_case_on_argv_mutation: false,
            mutation_guard: None,
        }
    }

    const fn patterned(argv_pattern: &'static pattern::ArgvPattern, scenario: ScenarioFn) -> Self {
        Self {
            argv_pattern: Some(argv_pattern),
            ..Self::generic(scenario)
        }
    }

    const fn with_mutator(mut self, mutation: MutationFn) -> Self {
        self.mutation = mutation;
        self
    }

    const fn with_candidate_guard(mut self, guard: fn(&[String]) -> bool) -> Self {
        self.candidate_guard = Some(guard);
        self
    }

    const fn with_resolvable_fixture(mut self, requires: fn(&[String]) -> bool) -> Self {
        self.resolvable_fixture = Some(requires);
        self
    }

    const fn with_profile(mut self, profile: UtilityProfile) -> Self {
        self.profile = profile;
        self
    }

    const fn with_system_state(mut self, generate: SystemStateFn) -> Self {
        self.system_state = generate;
        self
    }

    const fn with_case_normalizer(mut self, normalize: fn(&mut GeneratedCase)) -> Self {
        self.case_normalizer = Some(normalize);
        self
    }

    const fn with_cwd_policy(mut self, policy: CwdPolicy) -> Self {
        self.cwd_policy = policy;
        self
    }

    const fn with_case_regeneration_on_argv_mutation(mut self) -> Self {
        self.regenerate_case_on_argv_mutation = true;
        self
    }

    const fn with_mutation_guard(mut self, guard: fn(&[String]) -> bool) -> Self {
        self.mutation_guard = Some(guard);
        self
    }
}

impl InputGenerator for PatternInputGenerator {
    fn profile(&self) -> UtilityProfile {
        self.profile
    }

    fn generate_system_state(&self, rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint {
        (self.system_state)(rng, max_fs_entries)
    }

    fn generate_cwd(
        &self,
        rng: &mut StdRng,
        fixture: &FixtureBlueprint,
        mutation: bool,
    ) -> PathBuf {
        self.cwd_policy.generate(rng, fixture, mutation)
    }

    fn normalize_case(&self, case: &mut GeneratedCase) {
        if let Some(normalize) = self.case_normalizer {
            normalize(case);
        }
    }

    fn regenerate_case_on_argv_mutation(&self) -> bool {
        self.regenerate_case_on_argv_mutation
    }

    fn accepts_mutation(&self, argv: &[String]) -> bool {
        self.mutation_guard.is_none_or(|guard| guard(argv))
    }

    fn generate_argv(
        &self,
        profile: &UtilityProfile,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
    ) -> Vec<String> {
        match self.argv_pattern {
            Some(argv_pattern) => {
                pattern::generate(argv_pattern, option_pool, rng, max_args, fixture)
            }
            None => pattern::generate_generic(profile, option_pool, rng, max_args, fixture),
        }
    }

    fn scenario_case(&self, iteration: usize) -> Option<GeneratedCase> {
        (self.scenario)(iteration)
    }

    fn mutate_argv(
        &self,
        util: &str,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
        argv: &mut Vec<String>,
    ) {
        (self.mutation)(util, option_pool, rng, max_args, fixture, argv);
    }

    fn has_utility_pattern(&self) -> bool {
        self.argv_pattern.is_some()
    }

    fn accepts_candidate(&self, argv: &[String]) -> bool {
        self.candidate_guard.is_none_or(|guard| guard(argv))
    }

    fn requires_resolvable_fixture(&self, argv: &[String]) -> bool {
        self.resolvable_fixture
            .is_some_and(|requires| requires(argv))
    }
}

fn generate_system_state(util: &str, rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint {
    match capability_for(util) {
        Some(capability) => capability
            .input_generator
            .generate_system_state(rng, max_fs_entries),
        None => system_state::random_system_state(rng, max_fs_entries),
    }
}

fn generate_cwd(
    util: &str,
    rng: &mut StdRng,
    fixture: &FixtureBlueprint,
    mutation: bool,
) -> PathBuf {
    match capability_for(util) {
        Some(capability) => capability
            .input_generator
            .generate_cwd(rng, fixture, mutation),
        None => fixture.random_cwd(rng),
    }
}

fn normalize_case(util: &str, case: &mut GeneratedCase) {
    if let Some(capability) = capability_for(util) {
        capability.input_generator.normalize_case(case);
        if capability.requires_root_cwd {
            case.cwd = PathBuf::from(".");
        }
    }
}

fn regenerate_case_on_argv_mutation(util: &str) -> bool {
    capability_for(util).is_some_and(|capability| {
        capability
            .input_generator
            .regenerate_case_on_argv_mutation()
    })
}

fn accepts_mutation(util: &str, argv: &[String]) -> bool {
    capability_for(util).is_none_or(|capability| capability.input_generator.accepts_mutation(argv))
}

/// Reports whether `util`'s generator accepts a candidate argv; unregistered utilities accept all.
pub(crate) fn accepts_candidate(util: &str, argv: &[String]) -> bool {
    capability_for(util).is_none_or(|capability| capability.input_generator.accepts_candidate(argv))
}

/// Reports whether `util`'s generator needs every fixture symbolic link to resolve for `argv`.
pub(crate) fn requires_resolvable_fixture(util: &str, argv: &[String]) -> bool {
    capability_for(util)
        .is_some_and(|capability| capability.input_generator.requires_resolvable_fixture(argv))
}

pub(crate) fn generate_argv(
    util: &str,
    profile: &UtilityProfile,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    match capability_for(util) {
        Some(capability) => {
            capability
                .input_generator
                .generate_argv(profile, option_pool, rng, max_args, fixture)
        }
        None => pattern::generate_generic(profile, option_pool, rng, max_args, fixture),
    }
}

pub(crate) fn scenario_case(util: &str, iteration: usize) -> Option<GeneratedCase> {
    capability_for(util)?
        .input_generator
        .scenario_case(iteration)
}

pub(crate) fn mutate_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    match capability_for(util) {
        Some(capability) => {
            capability
                .input_generator
                .mutate_argv(util, option_pool, rng, max_args, fixture, argv)
        }
        None => mutations::mutate_generic_argv(util, option_pool, rng, max_args, fixture, argv),
    }
}

#[cfg(test)]
pub(crate) fn generate_argv_for_test(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    generate_argv(
        util,
        &utility_profile(util),
        option_pool,
        rng,
        max_args,
        fixture,
    )
}

#[cfg(test)]
pub(crate) fn random_chmod_mode_for_test(rng: &mut StdRng) -> String {
    generators::chmod::random_chmod_mode(rng)
}

fn utility_profile(util: &str) -> UtilityProfile {
    if let Some(capability) = capability_for(util) {
        return capability.input_generator.profile();
    }
    // Retain generic generation preferences for utilities without a registered generator.
    match util {
        "chown" | "chgrp" | "mkdir" | "rmdir" | "rm" | "cp" | "install" => UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        },
        _ => UtilityProfile {
            requires_path_operand: false,
            prefers_existing_paths: false,
        },
    }
}
