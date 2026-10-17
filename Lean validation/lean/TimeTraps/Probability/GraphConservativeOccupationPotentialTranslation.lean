module

public import TimeTraps.Probability.GraphConservativeOccupationPotentialPair

@[expose] public section

/-! Exact elapsed-time translation and time/state integration for the
actual graph Kac pairing. Continuous linear evaluation of the genuine
Bochner potential supplies the integration interchange. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationPotential_translate
    (P : GraphShiftedContactOperatorProblem V E) (g : C(GraphRealization P.geometry, ℝ))
    {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, P.realizedFeller (t.toNNReal - s.toNNReal) g) =
      P.occupationPotential g (T - s) := by
  have he {t : ℝ} (ht : s ≤ t) : t.toNNReal - s.toNNReal = (t - s).toNNReal := by
    calc
      _ = (((t.toNNReal : ℝ) - (s.toNNReal : ℝ))).toNNReal := NNReal.sub_def
      _ = _ := by rw [Real.coe_toNNReal t (hs.trans ht), Real.coe_toNNReal s hs]
  calc
    _ = ∫ t in s..T, P.realizedFeller (t - s).toNNReal g := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hsT] at ht
      exact congrArg (fun r : ℝ≥0 => P.realizedFeller r g) (he ht.1)
    _ = _ := by
      simpa only [sub_self, occupationPotential] using
        intervalIntegral.integral_comp_sub_right (a := s) (b := T)
          (fun r : ℝ => P.realizedFeller r.toNNReal g) s

theorem GraphShiftedContactOperatorProblem.occupationPair_integral_potential
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (f g : C(GraphRealization P.geometry, ℝ)) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, markovOccupationPair P.realizedTransition x f g s.toNNReal t.toNNReal) =
      ∫ y, f y * P.occupationPotential g (T - s) y ∂P.realizedTransition s.toNNReal x := by
  have hi : IntervalIntegrable
      (fun t : ℝ => P.realizedFeller (t.toNNReal - s.toNNReal) g) volume s T :=
    ((P.realizedFeller_strong_continuous g).comp
      (continuous_real_toNNReal.sub continuous_const)).intervalIntegrable s T
  calc
    _ = ∫ t in s..T, P.occupationPairingL s.toNNReal x f
        (P.realizedFeller (t.toNNReal - s.toNNReal) g) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact P.occupationPairingL_markovPair _ _ x f g
    _ = P.occupationPairingL s.toNNReal x f
        (∫ t in s..T, P.realizedFeller (t.toNNReal - s.toNNReal) g) :=
      (P.occupationPairingL s.toNNReal x f).intervalIntegral_comp_comm hi
    _ = P.occupationPairingL s.toNNReal x f (P.occupationPotential g (T - s)) :=
      congrArg (P.occupationPairingL s.toNNReal x f) (P.occupationPotential_translate g hs hsT)
    _ = _ := P.occupationPairingL_apply s.toNNReal x f _

end TimeTraps.Analysis
