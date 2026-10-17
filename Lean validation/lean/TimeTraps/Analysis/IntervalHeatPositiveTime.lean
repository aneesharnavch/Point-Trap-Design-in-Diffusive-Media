module

public import TimeTraps.Analysis.CompactSpectralSemigroupSmoothingDerivative
public import TimeTraps.Analysis.GeneralIntervalPointHeat
public import TimeTraps.Analysis.IntervalDirichletHeat
public import TimeTraps.Analysis.IntervalPeriodicHeat

@[expose] public section

/-! Heat evolution from every original L2 initial state is differentiable
at positive times and satisfies the actual full physical weak equation.
The independent reflecting/Robin, absorbing and periodic H1 test classes
are retained. No initial operator-domain regularity is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem IntervalPointProblem.heat_differentiableAt_of_pos (P : IntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (P.heatCurve x) s :=
  (P.compactPositiveInverse.heatCurve_hasDerivAt_of_pos x hs).differentiableAt

theorem IntervalPointProblem.heat_deriv_graph_of_pos (P : IntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    (P.heatCurve x s, -deriv (P.heatCurve x) s) ∈ P.operator.graph :=
  P.compactPositiveInverse.heatCurve_graph_deriv_of_pos x hs

theorem IntervalPointProblem.heat_deriv_norm_le (P : IntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ‖deriv (P.heatCurve x) s‖ ≤ ‖x‖ / s :=
  P.compactPositiveInverse.heatCurve_deriv_norm_le x hs

theorem IntervalPointProblem.heat_physical_of_pos (P : IntervalPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ∃ U : ℝ → ℝ, IntervalEnergy U l r ∧
      P.heatCurve x s =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ y in l..r, (-deriv (P.heatCurve x) s) y * v y := by
  let f := -deriv (P.heatCurve x) s
  refine ⟨(P.solution f).representative P.interval_pos,
    ((P.solution f).representative_spec P.interval_pos).1, ?_, P.solution_physical f⟩
  have he := (P.operator_graph_iff _ f).mp (P.heat_deriv_graph_of_pos x hs)
  rw [← he, P.inverse_apply]
  exact ((P.solution f).representative_spec P.interval_pos).2.1

theorem DirichletPointProblem.heat_differentiableAt_of_pos (P : DirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (P.heatCurve x) s :=
  (P.compactPositiveInverse.heatCurve_hasDerivAt_of_pos x hs).differentiableAt

theorem DirichletPointProblem.heat_deriv_graph_of_pos (P : DirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    (P.heatCurve x s, -deriv (P.heatCurve x) s) ∈ P.operator.graph :=
  P.compactPositiveInverse.heatCurve_graph_deriv_of_pos x hs

theorem DirichletPointProblem.heat_deriv_norm_le (P : DirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ‖deriv (P.heatCurve x) s‖ ≤ ‖x‖ / s :=
  P.compactPositiveInverse.heatCurve_deriv_norm_le x hs

theorem DirichletPointProblem.heat_physical_of_pos (P : DirichletPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ∃ U : ℝ → ℝ, IntervalEnergy U l r ∧
      (∀ y ∈ P.boundary.zero_sites, U y = 0) ∧
      P.heatCurve x s =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r → (∀ y ∈ P.boundary.zero_sites, v y = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ y in l..r, (-deriv (P.heatCurve x) s) y * v y :=
  (P.operator_graph_iff_exists_physical _ _).mp (P.heat_deriv_graph_of_pos x hs)

theorem PeriodicPointProblem.heat_differentiableAt_of_pos (P : PeriodicPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (P.heatCurve x) s :=
  (P.compactPositiveInverse.heatCurve_hasDerivAt_of_pos x hs).differentiableAt

theorem PeriodicPointProblem.heat_deriv_graph_of_pos (P : PeriodicPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    (P.heatCurve x s, -deriv (P.heatCurve x) s) ∈ P.operator.graph :=
  P.compactPositiveInverse.heatCurve_graph_deriv_of_pos x hs

theorem PeriodicPointProblem.heat_deriv_norm_le (P : PeriodicPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ‖deriv (P.heatCurve x) s‖ ≤ ‖x‖ / s :=
  P.compactPositiveInverse.heatCurve_deriv_norm_le x hs

theorem PeriodicPointProblem.heat_physical_of_pos (P : PeriodicPointProblem ι l r)
    (x : IntervalSobolevL2 l r) {s : ℝ} (hs : 0 < s) :
    ∃ U : ℝ → ℝ, IntervalEnergy U l r ∧ U l = U r ∧
      P.heatCurve x s =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ y in l..r, (-deriv (P.heatCurve x) s) y * v y :=
  (P.operator_graph_iff_exists_physical _ _).mp (P.heat_deriv_graph_of_pos x hs)

end TimeTraps.Analysis
