use std::collections::{HashMap, HashSet};

/* Test if a Result is Ok or Err */
pub fn test_result (r:Result<u64,u64>) -> bool {
    match r {
        Ok(_) => true,
        Err(_) => false
    }
}
