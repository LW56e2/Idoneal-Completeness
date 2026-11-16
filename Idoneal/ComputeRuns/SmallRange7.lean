import Idoneal.ComputeCore

/-! Kernel run: `small_range`, blocks 70..79 of 50000 numbers (see `small_range_of_runs`). -/

namespace Idoneal

theorem run_small_70 : rng 12 (70 * 50000) 50000 = true := by decide +kernel
theorem run_small_71 : rng 12 (71 * 50000) 50000 = true := by decide +kernel
theorem run_small_72 : rng 12 (72 * 50000) 50000 = true := by decide +kernel
theorem run_small_73 : rng 12 (73 * 50000) 50000 = true := by decide +kernel
theorem run_small_74 : rng 12 (74 * 50000) 50000 = true := by decide +kernel
theorem run_small_75 : rng 12 (75 * 50000) 50000 = true := by decide +kernel
theorem run_small_76 : rng 12 (76 * 50000) 50000 = true := by decide +kernel
theorem run_small_77 : rng 12 (77 * 50000) 50000 = true := by decide +kernel
theorem run_small_78 : rng 12 (78 * 50000) 50000 = true := by decide +kernel
theorem run_small_79 : rng 12 (79 * 50000) 50000 = true := by decide +kernel

end Idoneal
