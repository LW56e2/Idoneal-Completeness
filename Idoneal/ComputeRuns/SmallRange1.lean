import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 10..19 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_10 : rng 12 (10 * 50000) 50000 = true := by decide +kernel
theorem run_small_11 : rng 12 (11 * 50000) 50000 = true := by decide +kernel
theorem run_small_12 : rng 12 (12 * 50000) 50000 = true := by decide +kernel
theorem run_small_13 : rng 12 (13 * 50000) 50000 = true := by decide +kernel
theorem run_small_14 : rng 12 (14 * 50000) 50000 = true := by decide +kernel
theorem run_small_15 : rng 12 (15 * 50000) 50000 = true := by decide +kernel
theorem run_small_16 : rng 12 (16 * 50000) 50000 = true := by decide +kernel
theorem run_small_17 : rng 12 (17 * 50000) 50000 = true := by decide +kernel
theorem run_small_18 : rng 12 (18 * 50000) 50000 = true := by decide +kernel
theorem run_small_19 : rng 12 (19 * 50000) 50000 = true := by decide +kernel

end Idoneal
