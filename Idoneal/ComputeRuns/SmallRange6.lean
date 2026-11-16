import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 60..69 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_60 : rng 12 (60 * 50000) 50000 = true := by decide +kernel
theorem run_small_61 : rng 12 (61 * 50000) 50000 = true := by decide +kernel
theorem run_small_62 : rng 12 (62 * 50000) 50000 = true := by decide +kernel
theorem run_small_63 : rng 12 (63 * 50000) 50000 = true := by decide +kernel
theorem run_small_64 : rng 12 (64 * 50000) 50000 = true := by decide +kernel
theorem run_small_65 : rng 12 (65 * 50000) 50000 = true := by decide +kernel
theorem run_small_66 : rng 12 (66 * 50000) 50000 = true := by decide +kernel
theorem run_small_67 : rng 12 (67 * 50000) 50000 = true := by decide +kernel
theorem run_small_68 : rng 12 (68 * 50000) 50000 = true := by decide +kernel
theorem run_small_69 : rng 12 (69 * 50000) 50000 = true := by decide +kernel

end Idoneal
