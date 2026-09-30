use std::collections::BTreeMap;

const CONTROLLED_PROCESS_UMASKS: [u32; 5] = [0o000, 0o005, 0o022, 0o027, 0o077];
const CONTROLLED_PATH: &str = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin";

/// Selects the deterministic campaign umask for a seed and iteration.
pub fn selected_process_umask(seed: u64, iteration: usize) -> u32 {
    CONTROLLED_PROCESS_UMASKS
        [(seed as usize).wrapping_add(iteration) % CONTROLLED_PROCESS_UMASKS.len()]
}

/// Rejects process masks outside the Unix permission bits.
pub fn validate_process_umask(umask: u32) -> Result<(), String> {
    if umask > 0o777 {
        return Err(format!("process umask is out of range: {umask:04o}"));
    }
    Ok(())
}

/// Returns the canonical target environment for an approved campaign umask.
pub fn canonical_environment_config(umask: u32) -> Result<BTreeMap<String, String>, String> {
    if !CONTROLLED_PROCESS_UMASKS.contains(&umask) {
        return Err(format!("unsupported controlled process umask {umask:04o}"));
    }
    Ok(canonical_process_environment())
}

/// Returns the sorted, explicit environment shared by every target.
pub fn canonical_process_environment() -> BTreeMap<String, String> {
    BTreeMap::from([
        ("LANG".to_string(), "C".to_string()),
        ("LC_ALL".to_string(), "C".to_string()),
        ("PATH".to_string(), CONTROLLED_PATH.to_string()),
        ("QUOTING_STYLE".to_string(), "literal".to_string()),
        ("TERM".to_string(), "dumb".to_string()),
        ("TZ".to_string(), "UTC0".to_string()),
    ])
}

#[cfg(test)]
mod tests {
    use super::{
        canonical_environment_config, canonical_process_environment, selected_process_umask,
    };

    // Seed and iteration choose only an approved umask, deterministically.
    #[test]
    fn controlled_process_umask_selection_is_fixed_and_deterministic() {
        let selected = selected_process_umask(3, 9);

        assert_eq!(selected, selected_process_umask(3, 9));
        assert!([0o000, 0o005, 0o022, 0o027, 0o077].contains(&selected));
    }

    // The implementation campaign rejects unapproved umasks before spawning a target.
    #[test]
    fn controlled_process_environment_rejects_unknown_umask() {
        assert!(canonical_environment_config(0o777).is_err());
    }

    // Every target receives one explicit, secret-free environment map.
    #[test]
    fn controlled_environment_is_complete_and_secret_free() {
        assert_eq!(
            canonical_process_environment()
                .keys()
                .cloned()
                .collect::<Vec<_>>(),
            ["LANG", "LC_ALL", "PATH", "QUOTING_STYLE", "TERM", "TZ"]
        );
    }
}
