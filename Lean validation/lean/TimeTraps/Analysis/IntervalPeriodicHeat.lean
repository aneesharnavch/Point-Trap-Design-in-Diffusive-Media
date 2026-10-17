module

public import TimeTraps.Analysis.IntervalPeriodicPhysicalOperator
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization

@[expose] public section

/-! The generator of the actual interval heat evolution is exactly the
original weak periodic operator. This is an analytic correspondence;
no stochastic or order-preserving interpretation is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped NNReal

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def PeriodicPointProblem.heatCurve (P : PeriodicPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ) : IntervalSobolevL2 l r := P.compactPositiveInverse.heatCurve x t

theorem PeriodicPointProblem.heat_generator_iff_graph (P : PeriodicPointProblem ι l r)
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

theorem PeriodicPointProblem.heat_generator_iff_physical (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hup : u l = u r) :
    HasDerivWithinAt (P.heatCurve (P.boundary.stateL (P.boundary.ofEnergy hu hup.symm))) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        v l = v r →
        intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x :=
  (P.heat_generator_iff_graph _ f).trans (P.operator_graph_iff_physical f hu hup)

theorem PeriodicPointProblem.heat_initial (P : PeriodicPointProblem ι l r) (x : IntervalSobolevL2 l r) :
    P.heatCurve x 0 = x := P.compactPositiveInverse.heatCurve_zero x

theorem PeriodicPointProblem.heat_strong_continuous (P : PeriodicPointProblem ι l r) (x : IntervalSobolevL2 l r) :
    Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [PeriodicPointProblem.heatCurve, CompactPositiveInverse.heatCurve,
    Real.toNNReal_coe] using P.compactPositiveInverse.heatSemigroup_strong_continuous x

end TimeTraps.Analysis
