import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 20..29 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_20 : rng 12 (20 * 50000) 50000 = true := by decide +kernel
theorem run_small_21 : rng 12 (21 * 50000) 50000 = true := by decide +kernel
theorem run_small_22 : rng 12 (22 * 50000) 50000 = true := by decide +kernel
theorem run_small_23 : rng 12 (23 * 50000) 50000 = true := by decide +kernel
theorem run_small_24 : rng 12 (24 * 50000) 50000 = true := by decide +kernel
theorem run_small_25 : rng 12 (25 * 50000) 50000 = true := by decide +kernel
theorem run_small_26 : rng 12 (26 * 50000) 50000 = true := by decide +kernel
theorem run_small_27 : rng 12 (27 * 50000) 50000 = true := by decide +kernel
theorem run_small_28 : rng 12 (28 * 50000) 50000 = true := by decide +kernel
theorem run_small_29 : rng 12 (29 * 50000) 50000 = true := by decide +kernel

end Idoneal
