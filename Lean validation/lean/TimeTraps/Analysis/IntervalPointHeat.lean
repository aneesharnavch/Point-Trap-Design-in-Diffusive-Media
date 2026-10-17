module

public import TimeTraps.Analysis.IntervalPointOperator
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization

@[expose] public section

/-! The generator of the actual interval heat evolution is exactly the
original weak point-contact operator. This is an analytic correspondence;
no stochastic or order-preserving interpretation is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def UnitPointProblem.heatCurve (P : UnitPointProblem ι)
    (x : UnitIntervalL2) (t : ℝ) : UnitIntervalL2 := P.compactPositiveInverse.heatCurve x t

theorem UnitPointProblem.heat_generator_iff_graph (P : UnitPointProblem ι)
    (x f : UnitIntervalL2) :
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

theorem UnitPointProblem.heat_generator_iff_physical (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) :
    HasDerivWithinAt (P.heatCurve (ofEnergy hu zero_lt_one).state) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
        unitPointForm P.diffusivity P.strength P.site u v = ∫ x in (0 : ℝ)..1, f x * v x :=
  (P.heat_generator_iff_graph _ f).trans (P.operator_graph_iff_physical f hu)

theorem UnitPointProblem.heat_initial (P : UnitPointProblem ι) (x : UnitIntervalL2) :
    P.heatCurve x 0 = x := P.compactPositiveInverse.heatCurve_zero x

theorem UnitPointProblem.heat_strong_continuous (P : UnitPointProblem ι) (x : UnitIntervalL2) :
    Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [UnitPointProblem.heatCurve, CompactPositiveInverse.heatCurve,
    Real.toNNReal_coe] using P.compactPositiveInverse.heatSemigroup_strong_continuous x

end TimeTraps.Analysis
