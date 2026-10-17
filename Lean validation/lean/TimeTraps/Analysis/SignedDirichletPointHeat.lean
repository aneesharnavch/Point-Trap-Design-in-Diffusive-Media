module

public import TimeTraps.Analysis.SignedDirichletPointPhysical
public import TimeTraps.Analysis.ShiftedInverseHeatGenerator

@[expose] public section

/-! Heat evolution for arbitrary real point strengths and the selected
absorbing endpoints. The original unshifted operator is the exact right
generator; at positive times every L2 initial state satisfies the full
selected-zero physical weak equation. Negative and zero eigenvalues remain allowed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped NNReal

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedDirichletPointProblem.heatSemigroup (P : SignedDirichletPointProblem ι l r)
    (t : ℝ≥0) : IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  P.shiftedCompactPositiveInverse.translatedHeatSemigroup P.massShift t

noncomputable def SignedDirichletPointProblem.heatCurve (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ) : IntervalSobolevL2 l r :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve P.massShift x t

theorem SignedDirichletPointProblem.heatCurve_coe (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ≥0) : P.heatCurve x t = P.heatSemigroup t x :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_coe P.massShift x t

theorem SignedDirichletPointProblem.heatSemigroup_zero (P : SignedDirichletPointProblem ι l r) :
    P.heatSemigroup 0 = ContinuousLinearMap.id ℝ (IntervalSobolevL2 l r) :=
  P.shiftedCompactPositiveInverse.translatedHeatSemigroup_zero P.massShift

theorem SignedDirichletPointProblem.heatSemigroup_add (P : SignedDirichletPointProblem ι l r)
    (s t : ℝ≥0) : P.heatSemigroup (s + t) = (P.heatSemigroup s).comp (P.heatSemigroup t) :=
  P.shiftedCompactPositiveInverse.translatedHeatSemigroup_add P.massShift s t

theorem SignedDirichletPointProblem.heat_initial (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) : P.heatCurve x 0 = x :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_zero P.massShift x

theorem SignedDirichletPointProblem.heat_add (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (s t : ℝ≥0) :
    P.heatCurve x (s + t : ℝ≥0) = P.heatCurve (P.heatCurve x t) s := by
  change P.shiftedCompactPositiveInverse.translatedHeatCurve P.massShift x (s + t : ℝ≥0) = _
  simp only [heatCurve, CompactPositiveInverse.translatedHeatCurve_coe,
    P.shiftedCompactPositiveInverse.translatedHeatSemigroup_add,
    ContinuousLinearMap.comp_apply]

theorem SignedDirichletPointProblem.heat_strong_continuous (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) : Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [heatCurve, CompactPositiveInverse.translatedHeatCurve_coe] using
    P.shiftedCompactPositiveInverse.translatedHeatSemigroup_strong_continuous P.massShift x

theorem SignedDirichletPointProblem.heat_norm_le (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) (t : ℝ≥0) :
    ‖P.heatCurve x t‖ ≤ Real.exp (P.massShift * t) * ‖x‖ := by
  simpa only [heatCurve, CompactPositiveInverse.translatedHeatCurve_coe] using
    P.shiftedCompactPositiveInverse.translatedHeatSemigroup_norm_le P.massShift t x

theorem SignedDirichletPointProblem.heat_generator_iff_graph (P : SignedDirichletPointProblem ι l r)
    (x f : IntervalSobolevL2 l r) :
    HasDerivWithinAt (P.heatCurve x) (-f) (Ici 0) 0 ↔ (x, f) ∈ P.operator.graph :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_generator_iff_graph P.massShift x f

theorem SignedDirichletPointProblem.heat_generator_iff_physical
    (P : SignedDirichletPointProblem ι l r) (f : IntervalSobolevL2 l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    HasDerivWithinAt (P.heatCurve (P.boundary.stateL (P.boundary.ofEnergy hu huz))) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ y ∈ P.boundary.zero_sites, v y = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x :=
  (P.heat_generator_iff_graph _ f).trans (P.operator_graph_iff_physical f hu huz)

theorem SignedDirichletPointProblem.heat_mem_domain_of_pos (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    P.heatCurve x s ∈ P.operator.domain :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_mem_domain_of_pos P.massShift x hs

theorem SignedDirichletPointProblem.heat_hasDerivAt_of_pos (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (P.heatCurve x) (-P.operator ⟨P.heatCurve x s, P.heat_mem_domain_of_pos x hs⟩) s :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_hasDerivAt P.massShift x hs

theorem SignedDirichletPointProblem.heat_deriv_graph_of_pos (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    (P.heatCurve x s, -deriv (P.heatCurve x) s) ∈ P.operator.graph :=
  P.shiftedCompactPositiveInverse.translatedHeatCurve_deriv_graph P.massShift x hs

theorem SignedDirichletPointProblem.heat_physical_of_pos (P : SignedDirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ∃ U : ℝ → ℝ, IntervalEnergy U l r ∧
      (∀ y ∈ P.boundary.zero_sites, U y = 0) ∧
      P.heatCurve x s =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ y ∈ P.boundary.zero_sites, v y = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ y in l..r, (-deriv (P.heatCurve x) s) y * v y :=
  (P.operator_graph_iff_exists_physical _ _).mp (P.heat_deriv_graph_of_pos x hs)

end TimeTraps.Analysis
