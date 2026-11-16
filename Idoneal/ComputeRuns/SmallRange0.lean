import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 0..9 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_0 : rng 12 (0 * 50000) 50000 = true := by decide +kernel
theorem run_small_1 : rng 12 (1 * 50000) 50000 = true := by decide +kernel
theorem run_small_2 : rng 12 (2 * 50000) 50000 = true := by decide +kernel
theorem run_small_3 : rng 12 (3 * 50000) 50000 = true := by decide +kernel
theorem run_small_4 : rng 12 (4 * 50000) 50000 = true := by decide +kernel
theorem run_small_5 : rng 12 (5 * 50000) 50000 = true := by decide +kernel
theorem run_small_6 : rng 12 (6 * 50000) 50000 = true := by decide +kernel
theorem run_small_7 : rng 12 (7 * 50000) 50000 = true := by decide +kernel
theorem run_small_8 : rng 12 (8 * 50000) 50000 = true := by decide +kernel
theorem run_small_9 : rng 12 (9 * 50000) 50000 = true := by decide +kernel

end Idoneal
