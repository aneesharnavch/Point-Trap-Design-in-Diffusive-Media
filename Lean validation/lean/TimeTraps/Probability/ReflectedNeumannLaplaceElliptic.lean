module

public import TimeTraps.Probability.ReflectedNeumannLaplaceSpectrum

@[expose] public section

/-! The actual Laplace integral uniquely solves the genuine Neumann
operator resolvent equation for every alpha>0. Its representative solves
alpha*U-D*U''=f with AC/L2 slope and zero endpoint traces, and satisfies
the corresponding equation against every original H1 test. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedNeumannLaplace_unique (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α) (f u : ReflectedUniformL2 L hL)
    (hu : (reflectedUniformL2Equiv L hL u, reflectedUniformL2Equiv L hL (f - α • u)) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph) :
    u = reflectedNeumannLaplace L hL D α f := by
  have hg : (reflectedUniformL2Equiv L hL u, -reflectedUniformL2Equiv L hL (α • u - f)) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph := by
    simpa only [map_sub, map_smul, neg_sub] using hu
  apply (reflectedCosineHilbertBasis L hL).repr.injective
  apply lp.ext
  funext n
  simp only [HilbertBasis.repr_apply_apply]
  rw [reflectedNeumannLaplace_coefficient L hL D hD hα]
  have hc := reflectedNeumann_graph_generator_coefficients L hL D hD hg n
  rw [inner_sub_right, inner_smul_right] at hc
  have hr : 0 ≤ reflectedCosinePhysicalRate L D n := by
    unfold reflectedCosinePhysicalRate
    positivity
  apply (eq_div_iff (add_pos_of_pos_of_nonneg hα hr).ne').mpr
  nlinarith [hc]

theorem reflectedNeumannLaplace_elliptic_strong (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) :
    ∃ U j : ℝ → ℝ, reflectedNeumannLaplace L hL D α f =ᵐ[reflectedUniformLaw L hL] U ∧
      IntervalSlopeRegularity U j (fun x => (α * U x - f x) / D) 0 L ∧ j 0 = 0 ∧ j L = 0 := by
  obtain ⟨U, j, hu, hj, hleft, hright⟩ :=
    (reflectedPhysical_generator_iff_neumann_sobolev L hL D hD _ _).mp
      (reflectedNeumannLaplace_generator L hL D hD hα f)
  refine ⟨U, j, hu, ⟨hj.state_energy, hj.slope_energy, hj.slope_ae,
    hj.second_ae.trans ?_⟩, hleft, hright⟩
  have hsub := (reflectedUniformLaw_ae_iff L hL _).mp
    (Lp.coeFn_sub (α • reflectedNeumannLaplace L hL D α f) f)
  have hmul := (reflectedUniformLaw_ae_iff L hL _).mp
    (Lp.coeFn_smul α (reflectedNeumannLaplace L hL D α f))
  filter_upwards [hsub, hmul, (reflectedUniformLaw_ae_iff L hL _).mp hu] with x hs hm hx
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hm]
  simp only [Pi.smul_apply, smul_eq_mul, hx]

theorem reflectedNeumannLaplace_elliptic_weak (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) :
    ∃ U : ℝ → ℝ, IntervalEnergy U 0 L ∧
      reflectedNeumannLaplace L hL D α f =ᵐ[reflectedUniformLaw L hL] U ∧
      ∀ ψ : ℝ → ℝ, IntervalEnergy ψ 0 L →
        D * (∫ x in (0 : ℝ)..L, deriv U x * deriv ψ x) =
          ∫ x in (0 : ℝ)..L, (f x - α * U x) * ψ x := by
  obtain ⟨U, j, hu, hj, hleft, hright⟩ := reflectedNeumannLaplace_elliptic_strong L hL D hD hα f
  refine ⟨U, hj.state_energy, hu, fun ψ hψ => ?_⟩
  have he : (fun x => (α * U x - f x) / D) = (fun x => -(f x - α * U x) / D) := by
    funext x
    ring
  rw [he] at hj
  simpa only [hleft, hright, zero_mul, mul_zero, add_zero, sub_zero] using
    hj.poisson_green_identity hD.ne' hL.le hψ

end TimeTraps.Probability
