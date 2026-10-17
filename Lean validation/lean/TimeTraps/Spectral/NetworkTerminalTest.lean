module

public import TimeTraps.Spectral.NetworkFirstZero
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-! An explicit negative constant-vector test before the first edge pole.
This closes the finite positive-state existence argument without numerical roots. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

theorem cos_sub_one_div_sin {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    (Real.cos t - 1) / Real.sin t = -Real.tan (t / 2) := by
  have hs := Real.sin_two_mul (t / 2)
  have hc := Real.cos_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hs hc
  have hcp : 0 < Real.cos (t / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
  have hsp := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ne_of_gt hcp, ne_of_gt hsp]
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

variable {V E : Type*} [Fintype V] [Fintype E]

theorem SpectralNetwork.nodalForm_one (P : SpectralNetwork V E) {k : ℝ}
    (hk : 0 < k) (hp : P.BelowFirstPole k) :
    P.nodalForm k (fun _ => 1) = P.totalStrength -
      2 * P.diffusivity * k * ∑ e, Real.tan (k * P.length e / 2) := by
  have he (e : E) : P.edgeWeight k e * (Real.cos (k * P.length e) * (1 ^ 2 + 1 ^ 2) - 2 * 1 * 1) =
      -(2 * P.diffusivity * k * Real.tan (k * P.length e / 2)) := by
    rw [P.edgeWeight_eq hk]
    calc
      _ = 2 * P.diffusivity * k * ((Real.cos (k * P.length e) - 1) / Real.sin (k * P.length e)) := by ring
      _ = _ := by rw [cos_sub_one_div_sin ⟨mul_pos hk (P.length_pos e), hp.2 e⟩]; ring
  unfold nodalForm
  simp_rw [he]
  simp only [one_pow, mul_one, Finset.sum_neg_distrib, ← Finset.mul_sum]
  change -(2 * P.diffusivity * k * ∑ e, Real.tan (k * P.length e / 2)) + P.totalStrength = _
  ring

theorem SpectralNetwork.negative_nodal_test_exists [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) :
    ∃ B : ℝ, 0 < B ∧ P.BelowFirstPole B ∧ P.nodalForm B (fun _ => 1) < 0 := by
  obtain ⟨e, _, hmax⟩ := Finset.univ.exists_max_image P.length Finset.univ_nonempty
  let m := P.length e
  let t := 1 + P.totalStrength * m / (P.diffusivity * Real.pi)
  let B := 2 * Real.arctan t / m
  have hm : 0 < m := P.length_pos e
  have hDπ : 0 < P.diffusivity * Real.pi := mul_pos P.diffusivity_pos Real.pi_pos
  have ht : 1 < t := by
    dsimp [t]
    exact lt_add_of_pos_right _ (div_pos (mul_pos P.totalStrength_pos hm) hDπ)
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ha : Real.pi / 4 < Real.arctan t := by
    simpa only [Real.arctan_one] using Real.arctan_strictMono ht
  have hB : 0 < B := div_pos (mul_pos (by norm_num) (Real.arctan_pos.mpr ht0)) hm
  have hBm : B * m = 2 * Real.arctan t := by
    dsimp only [B]
    exact div_mul_cancel₀ _ (ne_of_gt hm)
  have hBp : P.BelowFirstPole B := by
    refine ⟨hB.le, ?_⟩
    intro d
    have hle : B * P.length d ≤ B * m :=
      mul_le_mul_of_nonneg_left (hmax d (Finset.mem_univ d)) hB.le
    have hu : B * m < Real.pi := by rw [hBm]; linarith [Real.arctan_lt_pi_div_two t]
    exact hle.trans_lt hu
  have htan : Real.tan (B * P.length e / 2) = t := by
    change Real.tan (B * m / 2) = t
    rw [hBm, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.tan_arctan]
  have hs : t ≤ ∑ d, Real.tan (B * P.length d / 2) := by
    rw [← htan]
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun d : E => Real.tan (B * P.length d / 2)) (a := e)
    · intro d _
      exact (Real.tan_pos_of_pos_of_lt_pi_div_two
        (div_pos (mul_pos hB (P.length_pos d)) (by norm_num)) (by linarith [hBp.2 d])).le
    · exact Finset.mem_univ e
  have htcalc : P.diffusivity * Real.pi * t =
      P.diffusivity * Real.pi + P.totalStrength * m := by
    dsimp only [t]
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hDπ)]
  have hangle : Real.pi < 2 * B * m := by nlinarith [hBm, ha]
  have hprod := mul_lt_mul_of_pos_left hangle (mul_pos P.diffusivity_pos ht0)
  have hscaled : P.totalStrength * m < (2 * P.diffusivity * B * t) * m := by
    nlinarith [htcalc]
  have hK : P.totalStrength < 2 * P.diffusivity * B * t :=
    lt_of_mul_lt_mul_right hscaled hm.le
  have htotal : 2 * P.diffusivity * B * t ≤
      2 * P.diffusivity * B * ∑ d, Real.tan (B * P.length d / 2) :=
    mul_le_mul_of_nonneg_left hs
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) P.diffusivity_pos) hB).le
  refine ⟨B, hB, hBp, ?_⟩
  rw [P.nodalForm_one hB hBp]
  linarith

theorem SpectralNetwork.positive_nodal_state_exists [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) :
    ∃ k : ℝ, 0 < k ∧ P.BelowFirstPole k ∧ (∀ W, 0 ≤ P.nodalForm k W) ∧
      ∃ U : V → ℝ, (∀ v, 0 < U v) ∧ ∀ v, P.nodalOperator k U v = 0 := by
  obtain ⟨B, hB, hpB, hneg⟩ := P.negative_nodal_test_exists
  obtain ⟨k, hk, hpk, hpos, U, hU, hop⟩ :=
    P.positive_nodal_state_of_terminal_test hB hpB hneg.le
  exact ⟨k, hk.1, hpk, hpos, U, hU, hop⟩

end TimeTraps.Spectral
