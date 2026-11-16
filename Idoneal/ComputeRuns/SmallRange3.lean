import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 30..39 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_30 : rng 12 (30 * 50000) 50000 = true := by decide +kernel
theorem run_small_31 : rng 12 (31 * 50000) 50000 = true := by decide +kernel
theorem run_small_32 : rng 12 (32 * 50000) 50000 = true := by decide +kernel
theorem run_small_33 : rng 12 (33 * 50000) 50000 = true := by decide +kernel
theorem run_small_34 : rng 12 (34 * 50000) 50000 = true := by decide +kernel
theorem run_small_35 : rng 12 (35 * 50000) 50000 = true := by decide +kernel
theorem run_small_36 : rng 12 (36 * 50000) 50000 = true := by decide +kernel
theorem run_small_37 : rng 12 (37 * 50000) 50000 = true := by decide +kernel
theorem run_small_38 : rng 12 (38 * 50000) 50000 = true := by decide +kernel
theorem run_small_39 : rng 12 (39 * 50000) 50000 = true := by decide +kernel

end Idoneal
