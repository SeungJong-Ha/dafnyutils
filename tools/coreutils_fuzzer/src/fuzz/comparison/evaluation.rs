//! Verdicts for observable differential comparison. Time behavior is unsupported.

use super::CompareResult;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum CaseVerdict {
    Match,
    Mismatch,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct EvaluatedComparison {
    pub(crate) execution: Option<crate::fuzz::execution::ExecutionEvidence>,
    pub(crate) observable: CompareResult,
}

impl EvaluatedComparison {
    pub(crate) fn new(observable: CompareResult) -> Self {
        Self {
            execution: None,
            observable,
        }
    }

    pub(crate) fn reproduces(&self, saved: &Self) -> bool {
        self.observable == saved.observable
    }

    pub(crate) fn verdict(&self) -> CaseVerdict {
        match self.observable {
            CompareResult::Match => CaseVerdict::Match,
            CompareResult::Mismatch { .. } => CaseVerdict::Mismatch,
        }
    }
}
