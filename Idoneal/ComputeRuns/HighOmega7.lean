import Idoneal.ComputeCore

/-! Kernel run: `high_omega`, k = 7, pieces c1-c8 (see `high_omega_of_runs`). -/

namespace Idoneal

theorem run_c1 : segB 210000000 1 210 8 19 = true := by decide +kernel
theorem run_c2 : segB 210000000 1 210 19 210000000 = true := by decide +kernel
theorem run_c3 : segB 210000000 2 30 6 7 = true := by decide +kernel
theorem run_c4 : segB 210000000 2 30 8 210000000 = true := by decide +kernel
theorem run_c5 : segB 210000000 3 6 4 5 = true := by decide +kernel
theorem run_c6 : segB 210000000 3 6 6 210000000 = true := by decide +kernel
theorem run_c7 : segB 210000000 4 2 4 210000000 = true := by decide +kernel
theorem run_c8 : segB 210000000 5 1 3 210000000 = true := by decide +kernel

end Idoneal
