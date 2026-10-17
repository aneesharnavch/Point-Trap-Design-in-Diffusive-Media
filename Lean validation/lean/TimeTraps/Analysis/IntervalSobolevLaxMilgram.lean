module

public import TimeTraps.Analysis.IntervalSobolevForm
public import TimeTraps.Analysis.IntervalSobolevSpacePairing
public import TimeTraps.Analysis.IntervalEnergyFormCongruence
public import TimeTraps.Analysis.LaxMilgram

@[expose] public section

/-!
The actual Hilbert-space Lax--Milgram proof for the original unit-interval
point-interaction equation, transferred to every AC/L2 test function.
Uniqueness is on the closed physical interval; exterior extensions remain
arbitrary. No solution or compactness premise is part of the construction.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped BigOperators

theorem unitSobolevForm_ofEnergy {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u 0 1) (hv : IntervalEnergy v 0 1) :
    unitSobolevForm D κ z hz (ofEnergy hu zero_lt_one) (ofEnergy hv zero_lt_one) =
      unitPointForm D κ z u v := by
  rw [unitSobolevForm_apply]
  exact unitPointForm_congr D κ z hz
    (representative_ofEnergy hu zero_lt_one) (representative_ofEnergy hv zero_lt_one)

theorem unitSobolevSource_ofEnergy {v : ℝ → ℝ} (hv : IntervalEnergy v 0 1) :
    unitSobolevSource (ofEnergy hv zero_lt_one) = ∫ x in (0 : ℝ)..1, v x :=
  (unitSobolevSource_apply _).trans (unitSource_congr (representative_ofEnergy hv zero_lt_one))

/-- The bundled variational equation is exactly the original equation with
all signed AC/L2 test functions. -/
theorem unitSobolev_weak_iff {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) :
    (∀ v : UnitIntervalSobolev,
      unitSobolevForm D κ z hz (ofEnergy hu zero_lt_one) v = unitSobolevSource v) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
      unitPointForm D κ z u v = ∫ x in (0 : ℝ)..1, v x) := by
  constructor
  · intro h v hv
    have he := h (ofEnergy hv zero_lt_one)
    rwa [unitSobolevForm_ofEnergy D κ z hz hu hv, unitSobolevSource_ofEnergy hv] at he
  · intro h v
    rw [unitSobolevForm_apply, unitSobolevSource_apply]
    rw [unitPointForm_congr D κ z hz (representative_ofEnergy hu zero_lt_one)
      (fun _ _ => rfl)]
    exact h (v.representative zero_lt_one) (v.representative_spec zero_lt_one).1

theorem unit_hilbert_lax_milgram_existsUnique {ι : Type*} [Fintype ι]
    {D : ℝ} (hD : 0 < D) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1) (k : ι) (hκk : 0 < κ k) :
    ∃! u : UnitIntervalSobolev, ∀ v : UnitIntervalSobolev,
      unitSobolevForm D κ z hz u v = unitSobolevSource v :=
  coercive_form_existsUnique _ (unitSobolevForm_coercive hD κ z hκ hz k hκk) _

/-- Existence and complete physical uniqueness obtained by the actual
Hilbert-space argument from the source. -/
theorem unit_energy_lax_milgram_exists_unique {ι : Type*} [Fintype ι]
    {D : ℝ} (hD : 0 < D) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1) (k : ι) (hκk : 0 < κ k) :
    ∃ u : ℝ → ℝ, IntervalEnergy u 0 1 ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
        unitPointForm D κ z u v = ∫ x in (0 : ℝ)..1, v x) ∧
      ∀ w : ℝ → ℝ, IntervalEnergy w 0 1 →
        (∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
          unitPointForm D κ z w v = ∫ x in (0 : ℝ)..1, v x) →
        EqOn w u (Icc (0 : ℝ) 1) := by
  obtain ⟨u, hu, huniq⟩ := unit_hilbert_lax_milgram_existsUnique hD κ z hκ hz k hκk
  have hE := (u.representative_spec zero_lt_one).1
  refine ⟨u.representative zero_lt_one, hE, ?_, ?_⟩
  · apply (unitSobolev_weak_iff D κ z hz hE).mp
    rw [ofEnergy_representative u zero_lt_one]
    exact hu
  · intro w hw he
    have hb := (unitSobolev_weak_iff D κ z hz hw).mpr he
    have heq := huniq (ofEnergy hw zero_lt_one) hb
    have hp := representative_ofEnergy hw zero_lt_one
    rw [heq] at hp
    exact hp.symm

/-- The explicit source coercivity constant also bounds every weak
solution in the actual H1 norm. -/
theorem unit_energy_lax_milgram_bound {ι : Type*} [Fintype ι]
    {D : ℝ} (hD : 0 < D) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1) (k : ι) (hκk : 0 < κ k)
    {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
      unitPointForm D κ z u v = ∫ x in (0 : ℝ)..1, v x) :
    intervalH1Size u 0 1 ≤ 1 / min (D / 3) (κ k / 2) := by
  have hcoerce : ∀ v : UnitIntervalSobolev,
      min (D / 3) (κ k / 2) * ‖v‖ ^ 2 ≤ unitSobolevForm D κ z hz v v := by
    intro v
    rw [unitSobolevForm_apply, v.norm_sq_eq_h1SizeSq zero_lt_one]
    exact (v.representative_spec zero_lt_one).1.unit_point_form_coercive hD.le hκ k (hz k)
  have hc := unitPointForm_coercivity_constant_pos hD hκk
  have hb := coercive_form_solution_bound _ unitSobolevSource hc hcoerce
    ((unitSobolev_weak_iff D κ z hz hu).mpr he)
  have hn : ‖ofEnergy hu zero_lt_one‖ = intervalH1Size u 0 1 := by
    rw [norm_eq_h1Size _ zero_lt_one]
    unfold intervalH1Size intervalH1SizeSq
    congr 2
    · exact unitSource_congr (fun x hx => congrArg (fun t : ℝ => t ^ 2)
        (representative_ofEnergy hu zero_lt_one hx))
    · apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro x hx
      change deriv ((ofEnergy hu zero_lt_one).representative zero_lt_one) x ^ 2 = deriv u x ^ 2
      rw [((representative_ofEnergy hu zero_lt_one).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx]
  rw [hn] at hb
  exact hb.trans (div_le_div_of_nonneg_right unitSobolevSource_norm_le hc.le)

end TimeTraps.Analysis
