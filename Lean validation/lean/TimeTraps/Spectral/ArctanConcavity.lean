module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Exact differential calculation and strict Jensen inequality for positive trap strengths. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

noncomputable def scaledArctan (c t : ℝ) : ℝ := Real.arctan (t / c)

theorem scaledArctan_hasDerivAt {c : ℝ} (hc : 0 < c) (t : ℝ) :
    HasDerivAt (scaledArctan c) (c / (c ^ 2 + t ^ 2)) t := by
  have h := ((hasDerivAt_id t).div_const c).arctan
  change HasDerivAt (scaledArctan c) (1 / (1 + (t / c) ^ 2) * (1 / c)) t at h
  convert h using 1
  field_simp

theorem scaledArctan_deriv {c : ℝ} (hc : 0 < c) :
    deriv (scaledArctan c) = fun t => c / (c ^ 2 + t ^ 2) :=
  funext fun t => (scaledArctan_hasDerivAt hc t).deriv

theorem scaledArctanSlope_hasDerivAt {c : ℝ} (hc : 0 < c) (t : ℝ) :
    HasDerivAt (fun t => c / (c ^ 2 + t ^ 2))
      (-2 * c * t / (c ^ 2 + t ^ 2) ^ 2) t := by
  have hd : c ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t))
  have h := (hasDerivAt_const t c).div
    ((hasDerivAt_const t (c ^ 2)).add ((hasDerivAt_id t).pow 2)) hd
  change HasDerivAt (fun t => c / (c ^ 2 + t ^ 2))
    ((0 * (c ^ 2 + t ^ 2) - c * (0 + 2 * t ^ (2 - 1) * 1)) / (c ^ 2 + t ^ 2) ^ 2) t at h
  convert h using 1
  ring

theorem scaledArctan_deriv_two {c : ℝ} (hc : 0 < c) (t : ℝ) :
    deriv^[2] (scaledArctan c) t = -2 * c * t / (c ^ 2 + t ^ 2) ^ 2 := by
  change deriv (deriv (scaledArctan c)) t = _
  rw [scaledArctan_deriv hc]
  exact (scaledArctanSlope_hasDerivAt hc t).deriv

theorem scaledArctan_deriv_two_neg {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    deriv^[2] (scaledArctan c) t < 0 := by
  rw [scaledArctan_deriv_two hc]
  apply div_neg_of_neg_of_pos
  · nlinarith
  · exact sq_pos_of_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t))

theorem scaledArctan_strictConcaveOn {c : ℝ} (hc : 0 < c) :
    StrictConcaveOn ℝ (Ioi 0) (scaledArctan c) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 0)
  · exact (Real.continuous_arctan.comp (continuous_id.div_const c)).continuousOn
  · intro t ht
    exact scaledArctan_deriv_two_neg hc ht

theorem scaledArctan_sum_le {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 < c)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, scaledArctan c (t i)) ≤ n * scaledArctan c ((∑ i, t i) / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hw : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by simp [ne_of_gt hn']
  have h := (scaledArctan_strictConcaveOn hc).concaveOn.le_map_sum
    (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := t)
    (fun _ _ => le_of_lt (inv_pos.mpr hn')) hw (fun i _ => ht i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have hm : (n : ℝ)⁻¹ * ∑ i, t i = (∑ i, t i) / n := by ring
  rw [hm] at h
  have := mul_le_mul_of_nonneg_left h hn'.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn'), one_mul] using this

theorem scaledArctan_sum_eq_iff {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 < c)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, scaledArctan c (t i)) = n * scaledArctan c ((∑ i, t i) / n) ↔
      ∀ i, t i = (∑ j, t j) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hw : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by simp [ne_of_gt hn']
  have h := (scaledArctan_strictConcaveOn hc).map_sum_eq_iff
    (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := t)
    (fun _ _ => inv_pos.mpr hn') hw (fun i _ => ht i)
  simp only [smul_eq_mul, ← Finset.mul_sum, Finset.mem_univ, forall_true_left] at h
  have hm : (n : ℝ)⁻¹ * ∑ i, t i = (∑ i, t i) / n := by ring
  rw [hm] at h
  rw [← h]
  constructor
  · intro he
    rw [he]
    field_simp
  · intro he
    rw [he]
    field_simp

end TimeTraps.Spectral
