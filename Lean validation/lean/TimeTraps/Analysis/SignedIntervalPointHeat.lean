module

public import TimeTraps.Analysis.SignedIntervalPointPhysical
public import TimeTraps.Analysis.ShiftedInverseHeatGenerator

@[expose] public section

/-! Heat evolution for arbitrary real point strengths. The original
unshifted operator is the exact right generator; at positive times every
L2 initial state satisfies the full physical weak equation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped NNReal

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedIntervalPointProblem.heatCurve (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ) : IntervalSobolevL2 l r :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve P.massShift x t

theorem SignedIntervalPointProblem.heat_initial (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) : P.heatCurve x 0 = x :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_zero P.massShift x

theorem SignedIntervalPointProblem.heat_add (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (s t : ℝ≥0) :
    P.heatCurve x (s + t : ℝ≥0) = P.heatCurve (P.heatCurve x t) s := by
  change P.shiftedCompactPositiveInverse.translatedHeatCurve P.massShift x (s + t : ℝ≥0) = _
  simp only [heatCurve, CompactPositiveInverse.translatedHeatCurve_coe,
    P.shiftedCompactPositiveInverse.translatedHeatSemigroup_add,
    ContinuousLinearMap.comp_apply]

theorem SignedIntervalPointProblem.heat_strong_continuous (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) : Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [heatCurve, CompactPositiveInverse.translatedHeatCurve_coe] using
    P.shiftedCompactPositiveInverse.translatedHeatSemigroup_strong_continuous P.massShift x

theorem SignedIntervalPointProblem.heat_norm_le (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ≥0) :
    ‖P.heatCurve x t‖ ≤ Real.exp (P.massShift * t) * ‖x‖ := by
  simpa only [heatCurve, CompactPositiveInverse.translatedHeatCurve_coe] using
    P.shiftedCompactPositiveInverse.translatedHeatSemigroup_norm_le P.massShift t x

theorem SignedIntervalPointProblem.heat_generator_iff_graph (P : SignedIntervalPointProblem ι l r)
    (x f : IntervalSobolevL2 l r) :
    HasDerivWithinAt (P.heatCurve x) (-f) (Ici 0) 0 ↔ (x, f) ∈ P.operator.graph :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_generator_iff_graph P.massShift x f

theorem SignedIntervalPointProblem.heat_generator_iff_physical
    (P : SignedIntervalPointProblem ι l r) (f : IntervalSobolevL2 l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    HasDerivWithinAt (P.heatCurve (ofEnergy hu P.interval_pos).state) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x :=
  (P.heat_generator_iff_graph _ f).trans (P.operator_graph_iff_physical f hu)

theorem SignedIntervalPointProblem.heat_mem_domain_of_pos (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    P.heatCurve x s ∈ P.operator.domain :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_mem_domain_of_pos P.massShift x hs

theorem SignedIntervalPointProblem.heat_hasDerivAt_of_pos (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (P.heatCurve x) (-P.operator ⟨P.heatCurve x s, P.heat_mem_domain_of_pos x hs⟩) s :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_hasDerivAt P.massShift x hs

theorem SignedIntervalPointProblem.heat_deriv_graph_of_pos (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    (P.heatCurve x s, -deriv (P.heatCurve x) s) ∈ P.operator.graph :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_deriv_graph P.massShift x hs

theorem SignedIntervalPointProblem.heat_physical_of_pos (P : SignedIntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ∃ U : ℝ → ℝ, IntervalEnergy U l r ∧
      P.heatCurve x s =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ y in l..r, (-deriv (P.heatCurve x) s) y * v y :=
  (P.operator_graph_iff_exists_physical _ _).mp (P.heat_deriv_graph_of_pos x hs)

end TimeTraps.Analysis
