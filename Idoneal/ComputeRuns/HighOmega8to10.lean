import Idoneal.ComputeCore

/-! Kernel run: `high_omega`, k = 8, 9, 10 (complete enumerations) (see `high_omega_of_runs`). -/

namespace Idoneal

theorem run_d1 : goodB 900000000 7 2 1 = true := by decide +kernel
theorem run_e1 : goodB 3900000000 8 2 1 = true := by decide +kernel
theorem run_f1 : goodB 17000000000 9 2 1 = true := by decide +kernel

end Idoneal
