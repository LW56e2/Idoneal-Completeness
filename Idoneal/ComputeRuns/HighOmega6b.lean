import Idoneal.ComputeCore

/-! Kernel run: `high_omega`, k = 6, pieces b7-b13 (see `high_omega_of_runs`). -/

namespace Idoneal

theorem run_b7 : segB 50000000 1 42 47 50000000 = true := by decide +kernel
theorem run_b8 : segB 50000000 2 6 4 5 = true := by decide +kernel
theorem run_b9 : segB 50000000 2 6 6 7 = true := by decide +kernel
theorem run_b10 : segB 50000000 2 6 8 50000000 = true := by decide +kernel
theorem run_b11 : segB 50000000 3 2 4 7 = true := by decide +kernel
theorem run_b12 : segB 50000000 3 2 7 50000000 = true := by decide +kernel
theorem run_b13 : segB 50000000 4 1 3 50000000 = true := by decide +kernel

end Idoneal
