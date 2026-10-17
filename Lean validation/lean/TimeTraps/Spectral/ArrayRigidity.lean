module

public import TimeTraps.Spectral.ArrayWeak
public import TimeTraps.Spectral.CircleRigidity

@[expose] public section

/-! Ground-state simplicity for arbitrary physical trap arrays. The reference
value is taken at the first trap, with no assumption that this trap is at 0. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

variable {n : ℕ} {P : PeriodicArray n}

theorem ArrayWeakEigenEquation.proportional_of_quadraticForm_eq {u v : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u) (hu₀ : u P.offset ≠ 0)
    (hv : P.Energy v) (he : P.quadraticForm v = P.principalValue * P.squareMass v) :
    EqOn v (fun x => (v P.offset / u P.offset) * u x) (Icc 0 P.length) := by
  have huN := hu.normalized
  rw [P.principalValue_eq_normalized] at huN
  have huN₀ : P.normalizeFunction u 0 ≠ 0 := by rwa [P.normalize_zero]
  have heN : P.normalized.periodicQuadraticForm (P.normalizeFunction v) =
      P.normalized.periodicPrincipalValue * P.normalized.periodicMass (P.normalizeFunction v) := by
    rw [P.normalize_quadraticForm hv, P.normalize_mass hv, ← P.principalValue_eq_normalized]
    exact he
  have hp := huN.proportional_of_quadraticForm_eq huN₀ (P.normalize_energy hv) heN
  simp only [P.normalize_zero] at hp
  exact P.eqOn_scalar_of_normalized hu.energy.2 hv.2 hp

theorem ArrayWeakEigenEquation.unique_scalar_of_quadraticForm_eq {u v : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u) (hu₀ : u P.offset ≠ 0)
    (hv : P.Energy v) (he : P.quadraticForm v = P.principalValue * P.squareMass v) :
    ∃! c : ℝ, EqOn v (fun x => c * u x) (Icc 0 P.length) := by
  refine ⟨v P.offset / u P.offset, hu.proportional_of_quadraticForm_eq hu₀ hv he, ?_⟩
  intro c hc
  exact (eq_div_iff hu₀).mpr (hc ⟨P.offset_mem.1, P.offset_mem.2.le⟩).symm

theorem PeriodicArray.squareMass_of_eq_scalar (P : PeriodicArray n)
    {u v : ℝ → ℝ} {c : ℝ} (h : EqOn v (fun x => c * u x) (Icc 0 P.length)) :
    P.squareMass v = c ^ 2 * P.squareMass u := by
  unfold squareMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  change v x ^ 2 = c ^ 2 * u x ^ 2
  rw [h (by simpa only [uIcc_of_le P.length_pos.le] using hx), mul_pow]

theorem ArrayWeakEigenEquation.unique_nonzero_scalar_of_quadraticForm_eq {u v : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u) (hu₀ : u P.offset ≠ 0)
    (hv : P.Energy v) (hm : 0 < P.squareMass v)
    (he : P.quadraticForm v = P.principalValue * P.squareMass v) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Icc 0 P.length) := by
  obtain ⟨c, hc, huniq⟩ := hu.unique_scalar_of_quadraticForm_eq hu₀ hv he
  have hcn : c ≠ 0 := by
    intro hz
    have hmass := P.squareMass_of_eq_scalar hc
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hmass
    exact (ne_of_gt hm) hmass
  exact ⟨c, ⟨hcn, hc⟩, fun d hd => huniq d hd.2⟩

theorem ArrayWeakEigenEquation.rayleigh_minimizer_unique_scalar {u v : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u) (hu₀ : u P.offset ≠ 0)
    (hv : P.Energy v) (hm : 0 < P.squareMass v)
    (hmin : P.quadraticForm v / P.squareMass v = P.principalValue) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Icc 0 P.length) := by
  apply hu.unique_nonzero_scalar_of_quadraticForm_eq hu₀ hv hm
  exact (div_eq_iff (ne_of_gt hm)).mp hmin

theorem ArrayWeakEigenEquation.weak_state_unique_scalar {u v : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u) (hu₀ : u P.offset ≠ 0)
    (hv : ArrayWeakEigenEquation P P.principalValue v) :
    ∃! c : ℝ, EqOn v (fun x => c * u x) (Icc 0 P.length) :=
  hu.unique_scalar_of_quadraticForm_eq hu₀ hv.energy hv.self_quadraticForm

theorem ArrayWeakEigenEquation.eqOn_of_first_value {u v : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u)
    (hv : ArrayWeakEigenEquation P P.principalValue v) (h₀ : u P.offset = v P.offset) :
    EqOn u v (Icc 0 P.length) := by
  obtain ⟨φ, hφ, hpos, _, _⟩ := P.positive_ground_state
  have hφ₀ := ne_of_gt (hpos P.offset ⟨P.offset_mem.1, P.offset_mem.2.le⟩)
  have heu := hφ.proportional_of_quadraticForm_eq hφ₀ hu.energy hu.self_quadraticForm
  have hev := hφ.proportional_of_quadraticForm_eq hφ₀ hv.energy hv.self_quadraticForm
  intro x hx
  rw [heu hx, hev hx, h₀]

theorem ArrayWeakEigenEquation.positive_of_first_value_pos {u : ℝ → ℝ}
    (hu : ArrayWeakEigenEquation P P.principalValue u) (h₀ : 0 < u P.offset) :
    ∀ x ∈ Icc 0 P.length, 0 < u x := by
  obtain ⟨φ, hφ, hpos, _, _⟩ := P.positive_ground_state
  have hφ₀ := hpos P.offset ⟨P.offset_mem.1, P.offset_mem.2.le⟩
  have he := hφ.proportional_of_quadraticForm_eq (ne_of_gt hφ₀) hu.energy hu.self_quadraticForm
  intro x hx
  rw [he hx]
  exact mul_pos (div_pos h₀ hφ₀) (hpos x hx)

theorem PeriodicArray.ground_state_simple (P : PeriodicArray n) :
    ∃ u : ℝ → ℝ, ArrayWeakEigenEquation P P.principalValue u ∧
      (∀ x ∈ Icc 0 P.length, 0 < u x) ∧
      (∀ v, ArrayWeakEigenEquation P P.principalValue v →
        ∃! c : ℝ, EqOn v (fun x => c * u x) (Icc 0 P.length)) ∧
      ∀ v, P.Energy v → 0 < P.squareMass v →
        P.quadraticForm v / P.squareMass v = P.principalValue →
        ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Icc 0 P.length) := by
  obtain ⟨u, hu, hpos, _, _⟩ := P.positive_ground_state
  have h₀ := ne_of_gt (hpos P.offset ⟨P.offset_mem.1, P.offset_mem.2.le⟩)
  exact ⟨u, hu, hpos, fun _ hv => hu.weak_state_unique_scalar h₀ hv,
    fun _ hv hm hmin => hu.rayleigh_minimizer_unique_scalar h₀ hv hm hmin⟩

end TimeTraps.Spectral
