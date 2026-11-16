import Idoneal.ComputeCore

/-! Kernel run: `high_omega`, k = 5, pieces a1-a6 (see `high_omega_of_runs`). -/

namespace Idoneal

theorem run_a1 : segB 13000000 0 30 6 79 = true := by decide +kernel
theorem run_a2 : segB 13000000 0 30 79 13000000 = true := by decide +kernel
theorem run_a3 : segB 13000000 1 6 4 5 = true := by decide +kernel
theorem run_a4 : segB 13000000 1 6 6 11 = true := by decide +kernel
theorem run_a5 : segB 13000000 1 6 11 29 = true := by decide +kernel
theorem run_a6 : segB 13000000 1 6 29 13000000 = true := by decide +kernel

end Idoneal
