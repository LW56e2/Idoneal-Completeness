import Idoneal.ComputeCore

/-! Kernel run: `high_omega`, k = 5, pieces a7-a13 (see `high_omega_of_runs`). -/

namespace Idoneal

theorem run_a7 : segB 13000000 1 10 6 37 = true := by decide +kernel
theorem run_a8 : segB 13000000 1 10 37 13000000 = true := by decide +kernel
theorem run_a9 : segB 13000000 2 2 4 5 = true := by decide +kernel
theorem run_a10 : segB 13000000 2 2 6 13000000 = true := by decide +kernel
theorem run_a11 : segB 13000000 2 3 4 7 = true := by decide +kernel
theorem run_a12 : segB 13000000 2 3 7 13000000 = true := by decide +kernel
theorem run_a13 : segB 13000000 3 1 4 13000000 = true := by decide +kernel

end Idoneal
