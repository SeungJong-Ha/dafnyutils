//! Observable result capture, comparison algorithms and case verdicts.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum CompareResult {
    Match,
    Mismatch {
        process_outcome_diff: Option<(
            compare::ProcessOutcomeEvidence,
            compare::ProcessOutcomeEvidence,
        )>,
        stdout_diff: bool,
        stderr_diff: bool,
        fs_diff: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiffOp {
    Equal(String),
    Remove(String),
    Add(String),
}

pub mod compare;
pub(crate) mod evaluation;
pub mod fs_snapshot;
pub(crate) mod process_outcome;
