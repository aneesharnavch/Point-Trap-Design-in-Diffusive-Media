module

public import TimeTraps.Analysis.StieltjesLocalSupport
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! The actual continuous Stieltjes function 1-exp(-K). No normalization
of K at zero or absolute continuity of its measure is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

noncomputable def stieltjesExponential (K : StieltjesFunction ℝ) (hK : Continuous K) :
    StieltjesFunction ℝ :=
  continuousStieltjesFunction (fun r => 1 - Real.exp (-K r))
    (fun _ _ h => sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (K.mono h))) 1)
    (continuous_const.sub (Real.continuous_exp.comp hK.neg))

theorem stieltjesExponential_apply (K : StieltjesFunction ℝ)
    (hK : Continuous K) (r : ℝ) :
    stieltjesExponential K hK r = 1 - Real.exp (-K r) := rfl

theorem stieltjesExponential_continuous (K : StieltjesFunction ℝ)
    (hK : Continuous K) : Continuous (stieltjesExponential K hK) :=
  continuous_const.sub (Real.continuous_exp.comp hK.neg)

theorem stieltjesExponential_measure_Ioc (K : StieltjesFunction ℝ)
    (hK : Continuous K) (s t : ℝ) :
    (stieltjesExponential K hK).measure (Ioc s t) =
      ENNReal.ofReal (Real.exp (-K s) - Real.exp (-K t)) := by
  rw [StieltjesFunction.measure_Ioc, stieltjesExponential_apply, stieltjesExponential_apply]
  congr 1
  ring

theorem stieltjesExponential_measure_singleton (K : StieltjesFunction ℝ)
    (hK : Continuous K) (r : ℝ) :
    (stieltjesExponential K hK).measure {r} = 0 := by
  exact continuousStieltjesFunction_measure_singleton _ _ _ r

end TimeTraps.Analysis
