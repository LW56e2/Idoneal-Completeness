import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 50..59 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_50 : rng 12 (50 * 50000) 50000 = true := by decide +kernel
theorem run_small_51 : rng 12 (51 * 50000) 50000 = true := by decide +kernel
theorem run_small_52 : rng 12 (52 * 50000) 50000 = true := by decide +kernel
theorem run_small_53 : rng 12 (53 * 50000) 50000 = true := by decide +kernel
theorem run_small_54 : rng 12 (54 * 50000) 50000 = true := by decide +kernel
theorem run_small_55 : rng 12 (55 * 50000) 50000 = true := by decide +kernel
theorem run_small_56 : rng 12 (56 * 50000) 50000 = true := by decide +kernel
theorem run_small_57 : rng 12 (57 * 50000) 50000 = true := by decide +kernel
theorem run_small_58 : rng 12 (58 * 50000) 50000 = true := by decide +kernel
theorem run_small_59 : rng 12 (59 * 50000) 50000 = true := by decide +kernel

end Idoneal
