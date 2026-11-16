import Idoneal.ComputeCore

/-! Kernel run: `high_omega`, k = 6, pieces b1-b6 (see `high_omega_of_runs`). -/

namespace Idoneal

theorem run_b1 : segB 50000000 0 210 8 193 = true := by decide +kernel
theorem run_b2 : segB 50000000 0 210 193 50000000 = true := by decide +kernel
theorem run_b3 : segB 50000000 1 30 6 7 = true := by decide +kernel
theorem run_b4 : segB 50000000 1 30 8 17 = true := by decide +kernel
theorem run_b5 : segB 50000000 1 30 17 50000000 = true := by decide +kernel
theorem run_b6 : segB 50000000 1 42 8 47 = true := by decide +kernel

end Idoneal
