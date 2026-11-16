import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 40..49 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_40 : rng 12 (40 * 50000) 50000 = true := by decide +kernel
theorem run_small_41 : rng 12 (41 * 50000) 50000 = true := by decide +kernel
theorem run_small_42 : rng 12 (42 * 50000) 50000 = true := by decide +kernel
theorem run_small_43 : rng 12 (43 * 50000) 50000 = true := by decide +kernel
theorem run_small_44 : rng 12 (44 * 50000) 50000 = true := by decide +kernel
theorem run_small_45 : rng 12 (45 * 50000) 50000 = true := by decide +kernel
theorem run_small_46 : rng 12 (46 * 50000) 50000 = true := by decide +kernel
theorem run_small_47 : rng 12 (47 * 50000) 50000 = true := by decide +kernel
theorem run_small_48 : rng 12 (48 * 50000) 50000 = true := by decide +kernel
theorem run_small_49 : rng 12 (49 * 50000) 50000 = true := by decide +kernel

end Idoneal
