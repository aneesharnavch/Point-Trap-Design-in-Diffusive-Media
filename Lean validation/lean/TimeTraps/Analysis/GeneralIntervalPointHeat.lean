module

public import TimeTraps.Analysis.GeneralIntervalPointOperator
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization

@[expose] public section

/-! The generator of the actual interval heat evolution is exactly the
original weak point-contact operator. This is an analytic correspondence;
no stochastic or order-preserving interpretation is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped NNReal

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def IntervalPointProblem.heatCurve (P : IntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ) : IntervalSobolevL2 l r := P.compactPositiveInverse.heatCurve x t

theorem IntervalPointProblem.heat_generator_iff_graph (P : IntervalPointProblem ι l r)
    (x f : IntervalSobolevL2 l r) :
    HasDerivWithinAt (P.heatCurve x) (-f) (Ici 0) 0 ↔ (x, f) ∈ P.operator.graph := by
  change HasDerivWithinAt (P.compactPositiveInverse.heatCurve x) (-f) (Ici 0) 0 ↔ _
  rw [P.compactPositiveInverse.heatCurve_generator_iff]
  constructor
  · rintro ⟨hx, he⟩
    have hf : f = P.operator ⟨x, hx⟩ := neg_injective he
    rw [P.operator_graph_iff, hf]
    exact inverseOperator_right_inverse P.inverse P.inverse_injective ⟨x, hx⟩
  · intro he
    have ht := (P.operator_graph_iff x f).mp he
    have hx : x ∈ P.operator.domain := ⟨f, ht⟩
    refine ⟨hx, ?_⟩
    apply congrArg Neg.neg
    apply P.inverse_injective
    exact ht.trans (inverseOperator_right_inverse P.inverse P.inverse_injective ⟨x, hx⟩).symm

theorem IntervalPointProblem.heat_generator_iff_physical (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    HasDerivWithinAt (P.heatCurve (ofEnergy hu P.interval_pos).state) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x :=
  (P.heat_generator_iff_graph _ f).trans (P.operator_graph_iff_physical f hu)

theorem IntervalPointProblem.heat_initial (P : IntervalPointProblem ι l r) (x : IntervalSobolevL2 l r) :
    P.heatCurve x 0 = x := P.compactPositiveInverse.heatCurve_zero x

theorem IntervalPointProblem.heat_strong_continuous (P : IntervalPointProblem ι l r) (x : IntervalSobolevL2 l r) :
    Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [IntervalPointProblem.heatCurve, CompactPositiveInverse.heatCurve,
    Real.toNNReal_coe] using P.compactPositiveInverse.heatSemigroup_strong_continuous x

end TimeTraps.Analysis
