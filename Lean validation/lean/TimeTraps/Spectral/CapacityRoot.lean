module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
The positive scalar root in `eq:spectral-root`, independently of spectral
theory. The coefficients `a j` are κ_j/(2D). This is a scalar theorem, not
an identification of this root with a Rayleigh infimum.
-/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {ι : Type*}

noncomputable def phaseCapacity (s : Finset ι) (a : ι → ℝ) (k : ℝ) : ℝ :=
  ∑ j ∈ s, 2 * Real.arctan (a j / k)

theorem phaseCapacity_continuousOn (s : Finset ι) (a : ι → ℝ) :
    ContinuousOn (phaseCapacity s a) (Set.Ioi 0) := by
  unfold phaseCapacity
  apply continuousOn_finsetSum
  intro j _
  apply continuousOn_const.mul
  apply Real.continuous_arctan.comp_continuousOn
  exact continuousOn_const.div continuousOn_id (fun k hk => ne_of_gt hk)

theorem phaseCapacity_strictAntiOn (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) :
    StrictAntiOn (phaseCapacity s a) (Set.Ioi 0) := by
  intro k hk l _ hkl
  have hterm : ∀ j ∈ s, 2 * Real.arctan (a j / l) < 2 * Real.arctan (a j / k) := by
    intro j hj
    exact mul_lt_mul_of_pos_left
      (Real.arctan_strictMono (div_lt_div_of_pos_left (ha j hj) hk hkl)) (by norm_num)
  obtain ⟨j, hj⟩ := hs
  exact Finset.sum_lt_sum (fun i hi => (hterm i hi).le) ⟨j, hj, hterm j hj⟩

/-- Comparison with the unique scalar root from a phase-sum inequality. -/
theorem le_capacity_root (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) {L k r : ℝ}
    (hL : 0 < L) (hk : 0 < k) (hr : 0 < r)
    (hroot : L * r = phaseCapacity s a r) (hbound : L * k ≤ phaseCapacity s a k) :
    k ≤ r := by
  by_contra h
  have hlt : r < k := lt_of_not_ge h
  have hcap := phaseCapacity_strictAntiOn s hs a ha hr hk hlt
  have hlength := mul_lt_mul_of_pos_left hlt hL
  linarith

theorem capacity_root_existsUnique (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) {L : ℝ} (hL : 0 < L) :
    ∃! k : ℝ, 0 < k ∧ L * k = phaseCapacity s a k := by
  obtain ⟨j, hj⟩ := hs
  have hs : s.Nonempty := ⟨j, hj⟩
  let lo := min (a j) (Real.pi / (4 * L))
  let upper := lo + ((s.card : ℝ) * Real.pi + 1) / L
  have hlo : 0 < lo := lt_min (ha j hj) (by positivity)
  have hstep : 0 < ((s.card : ℝ) * Real.pi + 1) / L := by positivity
  have horder : lo ≤ upper := by dsimp [upper]; linarith
  have hloSize : L * lo ≤ Real.pi / 4 := by
    have := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp (min_le_right (a j) (Real.pi / (4 * L)))
    dsimp [lo]
    linarith
  have hloTerm : Real.pi / 2 ≤ 2 * Real.arctan (a j / lo) := by
    have hratio : 1 ≤ a j / lo := (le_div_iff₀ hlo).mpr (by simpa only [one_mul] using (show lo ≤ a j from min_le_left _ _))
    have := Real.arctan_strictMono.monotone hratio
    rw [Real.arctan_one] at this
    linarith
  have hloCap : Real.pi / 2 ≤ phaseCapacity s a lo := by
    apply hloTerm.trans
    exact Finset.single_le_sum
      (fun i hi => mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr (div_nonneg (ha i hi).le hlo.le))) hj
  have hupperCap : phaseCapacity s a upper ≤ (s.card : ℝ) * Real.pi := by
    calc
      phaseCapacity s a upper ≤ ∑ _j ∈ s, Real.pi := by
        apply Finset.sum_le_sum
        intro i _
        linarith [Real.arctan_lt_pi_div_two (a i / upper)]
      _ = _ := by simp
  have hupperSize : (s.card : ℝ) * Real.pi < L * upper := by
    have hid : L * upper = L * lo + (s.card : ℝ) * Real.pi + 1 := by
      dsimp [upper]
      field_simp
      ring
    rw [hid]
    have := mul_pos hL hlo
    linarith
  have hc : ContinuousOn (fun k => phaseCapacity s a k - L * k) (Set.Icc lo upper) :=
    ((phaseCapacity_continuousOn s a).mono
      (fun k hk => lt_of_lt_of_le hlo hk.1)).sub (continuousOn_const.mul continuousOn_id)
  have hloResidual : 0 ≤ phaseCapacity s a lo - L * lo := by linarith [Real.pi_pos]
  have hupperResidual : phaseCapacity s a upper - L * upper ≤ 0 := by linarith
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc' horder hc ⟨hupperResidual, hloResidual⟩
  have hkpos : 0 < k := lt_of_lt_of_le hlo hk.1
  have hkroot : L * k = phaseCapacity s a k := by linarith
  refine ⟨k, ⟨hkpos, hkroot⟩, ?_⟩
  intro r hr
  exact le_antisymm
    (le_capacity_root s hs a ha hL hr.1 hkpos hkroot hr.2.le)
    (le_capacity_root s hs a ha hL hkpos hr.1 hr.2 hkroot.le)

/-- Positive lengths reconstructed from a scalar root sum to the interval length. -/
theorem capacity_cell_lengths (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ j ∈ s, 0 < a j) {L k : ℝ} (hk : 0 < k)
    (hroot : L * k = phaseCapacity s a k) :
    (∀ j ∈ s, 0 < 2 * Real.arctan (a j / k) / k) ∧
      (∑ j ∈ s, 2 * Real.arctan (a j / k) / k) = L := by
  constructor
  · intro j hj
    exact div_pos (mul_pos (by norm_num) (Real.arctan_pos.mpr (div_pos (ha j hj) hk))) hk
  · rw [← Finset.sum_div]
    change phaseCapacity s a k / k = L
    rw [← hroot, mul_div_cancel_right₀ L (ne_of_gt hk)]

/-- The scalar equation with the manuscript's physical strengths and diffusion constant. -/
theorem spectral_root_existsUnique (s : Finset ι) (hs : s.Nonempty)
    (κ : ι → ℝ) (hκ : ∀ j ∈ s, 0 < κ j) {D L : ℝ} (hD : 0 < D) (hL : 0 < L) :
    ∃! k : ℝ, 0 < k ∧ L * k = 2 * ∑ j ∈ s, Real.arctan (κ j / (2 * D * k)) := by
  have hc : ∀ k, phaseCapacity s (fun j => κ j / (2 * D)) k =
      2 * ∑ j ∈ s, Real.arctan (κ j / (2 * D * k)) := by
    intro k
    simp only [phaseCapacity, div_div, Finset.mul_sum]
  simpa only [hc] using capacity_root_existsUnique s hs (fun j => κ j / (2 * D))
    (fun j hj => div_pos (hκ j hj) (by positivity)) hL

end TimeTraps.Spectral
