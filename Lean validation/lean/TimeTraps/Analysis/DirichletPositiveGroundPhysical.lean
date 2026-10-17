module

public import TimeTraps.Analysis.DirichletPositiveGroundSimplicity

@[expose] public section

/-! Physical open-interval positivity and ground-state simplicity for the
existing Dirichlet/mixed model. Every selected zero trace and every test
with those traces is explicit. Contact strengths retain their existing
nonnegativity hypothesis, including the empty family. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem DirichletPointProblem.first_weak_hilbert
    (P : DirichletPointProblem ι l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        P.firstEigenvalue * ∫ x in l..r, u x * v x) :
    ∀ v : IntervalDirichletSpace P.boundary,
      P.form (P.boundary.ofEnergy hu huz) v = P.firstEigenvalue *
        inner ℝ (P.boundary.stateL (P.boundary.ofEnergy hu huz)) (P.boundary.stateL v) := by
  apply (P.hilbert_eigen_iff_physical (P.boundary.ofEnergy hu huz) P.firstEigenvalue).mpr
  intro v hv hvz
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem
    (P.boundary.ofEnergy_representative hu huz) (fun _ _ => rfl), he v hv hvz]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
  intro x hx
  change u x * v x = (P.boundary.ofEnergy hu huz).val.representative P.boundary.interval_pos x * v x
  rw [P.boundary.ofEnergy_representative hu huz (Ioo_subset_Icc_self hx)]

theorem DirichletPointProblem.first_weak_scalar
    (P : DirichletPointProblem ι l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ y ∈ P.boundary.zero_sites, u y = 0)
    (hvz : ∀ y ∈ P.boundary.zero_sites, v y = 0)
    {x : ℝ} (hx : x ∈ Ioo l r) (hu₀ : u x ≠ 0)
    (heu : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (∀ y ∈ P.boundary.zero_sites, w y = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u w =
        P.firstEigenvalue * ∫ y in l..r, u y * w y)
    (hev : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (∀ y ∈ P.boundary.zero_sites, w y = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r v w =
        P.firstEigenvalue * ∫ y in l..r, v y * w y) :
    EqOn v (fun y => (v x / u x) * u y) (Icc l r) := by
  have hUx := P.boundary.ofEnergy_representative hu huz (Ioo_subset_Icc_self hx)
  have hVx := P.boundary.ofEnergy_representative hv hvz (Ioo_subset_Icc_self hx)
  have hU₀ : (P.boundary.ofEnergy hu huz).val.representative P.boundary.interval_pos x ≠ 0 := by
    rwa [hUx]
  have he := P.first_hilbert_scalar (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hv hvz)
    hx hU₀ (P.first_weak_hilbert hu huz heu) (P.first_weak_hilbert hv hvz hev)
  rw [hUx, hVx] at he
  intro y hy
  have he' := congrArg (fun w : IntervalDirichletSpace P.boundary =>
    evalL P.boundary.interval_pos y hy w.val) he
  change evalL P.boundary.interval_pos y hy (P.boundary.ofEnergy hv hvz).val =
    evalL P.boundary.interval_pos y hy ((v x / u x) • (P.boundary.ofEnergy hu huz).val) at he'
  simp only [map_smul, smul_eq_mul] at he'
  change (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos y =
    (v x / u x) * (P.boundary.ofEnergy hu huz).val.representative P.boundary.interval_pos y at he'
  rwa [P.boundary.ofEnergy_representative hu huz hy,
    P.boundary.ofEnergy_representative hv hvz hy] at he'

theorem DirichletPointProblem.positive_first_physical (P : DirichletPointProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      ∃ huz : ∀ x ∈ P.boundary.zero_sites, u x = 0,
      (∀ x ∈ Ioo l r, 0 < u x) ∧ (∫ x in l..r, u x ^ 2) = 1 ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.firstEigenvalue * ∫ x in l..r, u x * v x) ∧
      (P.boundary.stateL (P.boundary.ofEnergy hu huz),
        P.firstEigenvalue • P.boundary.stateL (P.boundary.ofEnergy hu huz)) ∈ P.operator.graph := by
  obtain ⟨v, hp, hm, he⟩ := P.positive_first_eigenstate
  let u := v.val.representative P.boundary.interval_pos
  have hu : IntervalEnergy u l r := (v.val.representative_spec P.boundary.interval_pos).1
  have huz : ∀ x ∈ P.boundary.zero_sites, u x = 0 := fun _ hx => P.boundary.representative_zero v hx
  refine ⟨u, hu, huz, hp, ?_, (P.hilbert_eigen_iff_physical v P.firstEigenvalue).mp he, ?_⟩
  · change ‖v.val.state‖ ^ 2 = 1 at hm
    rw [← real_inner_self_eq_norm_sq, state_inner _ _ P.boundary.interval_pos] at hm
    simpa only [u, pow_two] using hm
  · rw [P.boundary.ofEnergy_representative_eq]
    exact (P.operator_eigen_iff_hilbert v P.firstEigenvalue).mpr he

end TimeTraps.Analysis
