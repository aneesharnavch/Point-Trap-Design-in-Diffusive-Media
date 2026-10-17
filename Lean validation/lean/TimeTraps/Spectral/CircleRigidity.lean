module

public import TimeTraps.Spectral.NetworkUniqueness
public import TimeTraps.Spectral.CircleWeak

@[expose] public section

/-! Ground-state uniqueness on the single physical periodic interval.
Equality is pointwise on [0,L] for arbitrary H1 representatives. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {n : ℕ} {C : CircleProblem n} {ev : ℝ}

theorem CircleProblem.eqOn_of_restriction_eq (C : CircleProblem n) {u v : ℝ → ℝ}
    (h : ∀ e, EqOn (C.restriction u e) (C.restriction v e) (Icc 0 (C.gap e))) :
    EqOn u v (Icc 0 C.length) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    intro x hx
    obtain ⟨e, he⟩ := C.cut.gap_cover hx
    have ht : x - C.site e ∈ Icc 0 (C.gap e) := by
      rw [← C.cut_gapLength]
      exact ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
    have hh := h e ht
    change u (C.site e + (x - C.site e)) = v (C.site e + (x - C.site e)) at hh
    simpa only [add_sub_cancel] using hh

theorem PeriodicWeakEigenEquation.self_quadraticForm {u : ℝ → ℝ}
    (h : PeriodicWeakEigenEquation C ev u) :
    C.periodicQuadraticForm u = ev * C.periodicMass u := by
  simpa only [CircleProblem.periodicQuadraticForm, CircleProblem.periodicMass,
    pow_two, mul_assoc] using h.weak_form u h.energy

theorem PeriodicWeakEigenEquation.proportional_of_quadraticForm_eq {u v : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u) (hu₀ : u 0 ≠ 0)
    (hv : C.PeriodicEnergy v)
    (he : C.periodicQuadraticForm v = C.periodicPrincipalValue * C.periodicMass v) :
    EqOn v (fun x => (v 0 / u 0) * u x) (Icc 0 C.length) := by
  let first : Fin n := ⟨0, C.count_pos⟩
  let : Nonempty (Fin n) := ⟨first⟩
  obtain ⟨F⟩ := C.network.principal_eigenstate_exists
  have hsite : C.site first = 0 := C.site_zero
  have huN := C.restricted_weak hu
  rw [C.periodicPrincipalValue_eq] at huN
  have hvN := C.restrict_periodic_energy hv
  have heN : C.network.quadraticForm (fun i => v (C.site i)) (C.restriction v) =
      C.network.principalValue * C.network.squareMass (C.restriction v) := by
    rw [C.restrict_quadraticForm hv.1, C.restrict_mass hv.1, ← C.periodicPrincipalValue_eq]
    exact he
  have heu := F.proportional_of_quadraticForm_eq huN.energy huN.self_quadraticForm first
  have hev := F.proportional_of_quadraticForm_eq hvN heN first
  apply C.eqOn_of_restriction_eq
  intro e x hx
  have h₁ := hev.2 e hx
  have h₂ := heu.2 e hx
  change v (C.site e + x) = (v (C.site first) / F.nodal first) * F.state e x at h₁
  change u (C.site e + x) = (u (C.site first) / F.nodal first) * F.state e x at h₂
  rw [hsite] at h₁ h₂
  change v (C.site e + x) = (v 0 / u 0) * u (C.site e + x)
  rw [h₁, h₂]
  field_simp [hu₀, ne_of_gt (F.nodal_positive first)]

theorem PeriodicWeakEigenEquation.unique_scalar_of_quadraticForm_eq {u v : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u) (hu₀ : u 0 ≠ 0)
    (hv : C.PeriodicEnergy v)
    (he : C.periodicQuadraticForm v = C.periodicPrincipalValue * C.periodicMass v) :
    ∃! c : ℝ, EqOn v (fun x => c * u x) (Icc 0 C.length) := by
  refine ⟨v 0 / u 0, hu.proportional_of_quadraticForm_eq hu₀ hv he, ?_⟩
  intro c hc
  exact (eq_div_iff hu₀).mpr (hc ⟨le_rfl, C.length_pos.le⟩).symm

theorem CircleProblem.periodicMass_of_eq_scalar (C : CircleProblem n)
    {u v : ℝ → ℝ} {c : ℝ} (h : EqOn v (fun x => c * u x) (Icc 0 C.length)) :
    C.periodicMass v = c ^ 2 * C.periodicMass u := by
  unfold periodicMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  change v x ^ 2 = c ^ 2 * u x ^ 2
  rw [h (by simpa only [uIcc_of_le C.length_pos.le] using hx), mul_pow]

theorem PeriodicWeakEigenEquation.unique_nonzero_scalar_of_quadraticForm_eq {u v : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u) (hu₀ : u 0 ≠ 0)
    (hv : C.PeriodicEnergy v) (hm : 0 < C.periodicMass v)
    (he : C.periodicQuadraticForm v = C.periodicPrincipalValue * C.periodicMass v) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Icc 0 C.length) := by
  obtain ⟨c, hc, huniq⟩ := hu.unique_scalar_of_quadraticForm_eq hu₀ hv he
  have hcn : c ≠ 0 := by
    intro hz
    have hmass := C.periodicMass_of_eq_scalar hc
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hmass
    exact (ne_of_gt hm) hmass
  exact ⟨c, ⟨hcn, hc⟩, fun d hd => huniq d hd.2⟩

theorem PeriodicWeakEigenEquation.rayleigh_minimizer_unique_scalar {u v : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u) (hu₀ : u 0 ≠ 0)
    (hv : C.PeriodicEnergy v) (hm : 0 < C.periodicMass v)
    (hmin : C.periodicQuadraticForm v / C.periodicMass v = C.periodicPrincipalValue) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Icc 0 C.length) := by
  apply hu.unique_nonzero_scalar_of_quadraticForm_eq hu₀ hv hm
  exact (div_eq_iff (ne_of_gt hm)).mp hmin

theorem PeriodicWeakEigenEquation.weak_state_unique_scalar {u v : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u) (hu₀ : u 0 ≠ 0)
    (hv : PeriodicWeakEigenEquation C C.periodicPrincipalValue v) :
    ∃! c : ℝ, EqOn v (fun x => c * u x) (Icc 0 C.length) :=
  hu.unique_scalar_of_quadraticForm_eq hu₀ hv.energy hv.self_quadraticForm

theorem PeriodicWeakEigenEquation.eqOn_of_initial_value {u v : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u)
    (hv : PeriodicWeakEigenEquation C C.periodicPrincipalValue v) (h₀ : u 0 = v 0) :
    EqOn u v (Icc 0 C.length) := by
  obtain ⟨φ, hφ, hpos, _, _⟩ := C.periodic_positive_ground_state
  have hφ₀ := ne_of_gt (hpos 0 ⟨le_rfl, C.length_pos.le⟩)
  have heu := hφ.proportional_of_quadraticForm_eq hφ₀ hu.energy hu.self_quadraticForm
  have hev := hφ.proportional_of_quadraticForm_eq hφ₀ hv.energy hv.self_quadraticForm
  intro x hx
  rw [heu hx, hev hx, h₀]

theorem PeriodicWeakEigenEquation.positive_of_initial_value_pos {u : ℝ → ℝ}
    (hu : PeriodicWeakEigenEquation C C.periodicPrincipalValue u) (h₀ : 0 < u 0) :
    ∀ x ∈ Icc 0 C.length, 0 < u x := by
  obtain ⟨φ, hφ, hpos, _, _⟩ := C.periodic_positive_ground_state
  have hφ₀ := hpos 0 ⟨le_rfl, C.length_pos.le⟩
  have he := hφ.proportional_of_quadraticForm_eq (ne_of_gt hφ₀) hu.energy hu.self_quadraticForm
  intro x hx
  rw [he hx]
  exact mul_pos (div_pos h₀ hφ₀) (hpos x hx)

theorem CircleProblem.periodic_ground_state_simple (C : CircleProblem n) :
    ∃ u : ℝ → ℝ, PeriodicWeakEigenEquation C C.periodicPrincipalValue u ∧
      (∀ x ∈ Icc 0 C.length, 0 < u x) ∧
      (∀ v, PeriodicWeakEigenEquation C C.periodicPrincipalValue v →
        ∃! c : ℝ, EqOn v (fun x => c * u x) (Icc 0 C.length)) ∧
      ∀ v, C.PeriodicEnergy v → 0 < C.periodicMass v →
        C.periodicQuadraticForm v / C.periodicMass v = C.periodicPrincipalValue →
        ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Icc 0 C.length) := by
  obtain ⟨u, hu, hpos, _, _⟩ := C.periodic_positive_ground_state
  have h₀ := ne_of_gt (hpos 0 ⟨le_rfl, C.length_pos.le⟩)
  exact ⟨u, hu, hpos, fun _ hv => hu.weak_state_unique_scalar h₀ hv,
    fun _ hv hm hmin => hu.rayleigh_minimizer_unique_scalar h₀ hv hm hmin⟩

end TimeTraps.Spectral
