import Idoneal.ComputeCore
import Idoneal.ComputeRuns.SmallRange0
import Idoneal.ComputeRuns.SmallRange1
import Idoneal.ComputeRuns.SmallRange2
import Idoneal.ComputeRuns.SmallRange3
import Idoneal.ComputeRuns.SmallRange4
import Idoneal.ComputeRuns.SmallRange5
import Idoneal.ComputeRuns.SmallRange6
import Idoneal.ComputeRuns.SmallRange7
import Idoneal.ComputeRuns.HighOmega5a
import Idoneal.ComputeRuns.HighOmega5b
import Idoneal.ComputeRuns.HighOmega6a
import Idoneal.ComputeRuns.HighOmega6b
import Idoneal.ComputeRuns.HighOmega7
import Idoneal.ComputeRuns.HighOmega8to10

/-!
# Kernel computations (blueprint §1 (K))

Statements below are the fixed interface. The checkers, their soundness and the assembly
theorems `small_range_of_runs`, `high_omega_of_runs` are in `Idoneal/ComputeCore.lean`; the
kernel runs (`decide +kernel`, no `native_decide`) are in `Idoneal/ComputeRuns/`.
-/

namespace Idoneal

theorem small_range {n : ℕ} (h0 : 0 < n) (hn : n < 4000000)
    (hnot : n ∉ knownIdonealNumbers) : HasTriple n := by
  refine small_range_of_runs (fun i hi => ?_) h0 hn hnot
  interval_cases i
  exacts [run_small_0, run_small_1, run_small_2, run_small_3, run_small_4, run_small_5,
    run_small_6, run_small_7, run_small_8, run_small_9, run_small_10, run_small_11,
    run_small_12, run_small_13, run_small_14, run_small_15, run_small_16, run_small_17,
    run_small_18, run_small_19, run_small_20, run_small_21, run_small_22, run_small_23,
    run_small_24, run_small_25, run_small_26, run_small_27, run_small_28, run_small_29,
    run_small_30, run_small_31, run_small_32, run_small_33, run_small_34, run_small_35,
    run_small_36, run_small_37, run_small_38, run_small_39, run_small_40, run_small_41,
    run_small_42, run_small_43, run_small_44, run_small_45, run_small_46, run_small_47,
    run_small_48, run_small_49, run_small_50, run_small_51, run_small_52, run_small_53,
    run_small_54, run_small_55, run_small_56, run_small_57, run_small_58, run_small_59,
    run_small_60, run_small_61, run_small_62, run_small_63, run_small_64, run_small_65,
    run_small_66, run_small_67, run_small_68, run_small_69, run_small_70, run_small_71,
    run_small_72, run_small_73, run_small_74, run_small_75, run_small_76, run_small_77,
    run_small_78, run_small_79]

theorem high_omega {n : ℕ} (hsf : Squarefree n) (hn : 4000000 ≤ n)
    (h : (n.primeFactors.card = 5 ∧ n < 13000000) ∨
      (n.primeFactors.card = 6 ∧ n < 50000000) ∨
      (n.primeFactors.card = 7 ∧ n < 210000000) ∨
      (n.primeFactors.card = 8 ∧ n < 900000000) ∨
      (n.primeFactors.card = 9 ∧ n < 3900000000) ∨
      (n.primeFactors.card = 10 ∧ n < 17000000000)) : HasTriple n :=
  high_omega_of_runs run_a1 run_a2 run_a3 run_a4 run_a5 run_a6 run_a7 run_a8 run_a9 run_a10
    run_a11 run_a12 run_a13 run_b1 run_b2 run_b3 run_b4 run_b5 run_b6 run_b7 run_b8 run_b9
    run_b10 run_b11 run_b12 run_b13 run_c1 run_c2 run_c3 run_c4 run_c5 run_c6 run_c7 run_c8
    run_d1 run_e1 run_f1 hsf hn h

end Idoneal
