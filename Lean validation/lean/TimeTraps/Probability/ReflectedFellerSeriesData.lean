module

public import TimeTraps.Probability.ReflectedFellerSeriesBounds

@[expose] public section

/-! The continuous-function heat series and its time derivative have
summable uniform majorants on every positive time neighborhood. These
are actual C([0,L])-valued series, not formal expansions. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped Topology

def reflectedFellerHeatTerm (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n : ℕ) (t : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  (2 * reflectedFellerPairing L hL (neumannCosine L (n + 1)) f *
    Real.exp (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2 * t)) • neumannCosine L (n + 1)

def reflectedFellerHeatTermDerivative (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n : ℕ) (t : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2) • reflectedFellerHeatTerm L hL D f n t

def reflectedFellerHeatSeries (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  reflectedFellerMean L hL f • 1 + ∑' n : ℕ, reflectedFellerHeatTerm L hL D f n t

theorem reflectedFellerHeatTerm_norm (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n : ℕ) (t : ℝ) :
    ‖reflectedFellerHeatTerm L hL D f n t‖ ≤ 2 * ‖f‖ *
      Real.exp (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2 * t) := by
  unfold reflectedFellerHeatTerm
  rw [norm_smul]
  calc
    _ ≤ ‖2 * reflectedFellerPairing L hL (neumannCosine L (n + 1)) f *
        Real.exp (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2 * t)‖ * 1 :=
      mul_le_mul_of_nonneg_left (reflectedFeller_cosine_norm_le_one L (n + 1)) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_one, norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (reflectedFellerPairing_cosine_norm L hL (n + 1) f) (by norm_num))
        (Real.exp_pos _).le

theorem reflectedFellerHeatTerm_bound (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n : ℕ) (δ t : ℝ) (ht : δ ≤ t) :
    ‖reflectedFellerHeatTerm L hL D f n t‖ ≤ 2 * ‖f‖ *
      Real.exp (-(reflectedFellerHeatRate L D * δ) * ((n + 1 : ℕ) : ℝ) ^ 2) :=
  (reflectedFellerHeatTerm_norm L hL D f n t).trans
    (mul_le_mul_of_nonneg_left (reflectedFeller_gaussian_decay_mono _
      (reflectedFellerHeatRate_pos L hL D hD).le (n + 1) δ t ht) (by positivity))

theorem reflectedFellerHeatTerm_summable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => reflectedFellerHeatTerm L hL D f n t) := by
  have hs := ((reflectedFeller_gaussian_weight_summable (reflectedFellerHeatRate L D * t)
    (mul_pos (reflectedFellerHeatRate_pos L hL D hD) ht) 0).mul_left (2 * ‖f‖)).comp_injective
    Nat.succ_injective
  simp only [pow_zero, one_mul] at hs
  exact hs.of_norm_bounded (fun n => reflectedFellerHeatTerm_bound L hL D hD f n t t le_rfl)

theorem reflectedFellerHeatTerm_hasDerivAt (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n : ℕ) (t : ℝ) :
    HasDerivAt (reflectedFellerHeatTerm L hL D f n) (reflectedFellerHeatTermDerivative L hL D f n t) t := by
  have hd := (((((hasDerivAt_id t).const_mul
    (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2)).exp).const_mul
      (2 * reflectedFellerPairing L hL (neumannCosine L (n + 1)) f)).smul_const (neumannCosine L (n + 1)))
  simp only [id_eq, mul_one] at hd
  apply hd.congr_deriv
  unfold reflectedFellerHeatTermDerivative reflectedFellerHeatTerm
  rw [smul_smul]
  congr 1
  ring

theorem reflectedFellerHeatTermDerivative_bound (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n : ℕ) (δ t : ℝ) (ht : δ ≤ t) :
    ‖reflectedFellerHeatTermDerivative L hL D f n t‖ ≤
      (2 * ‖f‖ * reflectedFellerHeatRate L D) * (((n + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (-(reflectedFellerHeatRate L D * δ) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  rw [reflectedFellerHeatTermDerivative, norm_smul, norm_mul, norm_neg,
    Real.norm_of_nonneg (reflectedFellerHeatRate_pos L hL D hD).le,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2) * (2 * ‖f‖ *
        Real.exp (-(reflectedFellerHeatRate L D * δ) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (reflectedFellerHeatTerm_bound L hL D hD f n δ t ht)
        (mul_nonneg (reflectedFellerHeatRate_pos L hL D hD).le (sq_nonneg _))
    _ = _ := by ring

theorem reflectedFellerHeatTermDerivative_majorant_summable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : C(Icc (0 : ℝ) L, ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℕ => (2 * ‖f‖ * reflectedFellerHeatRate L D) * (((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-(reflectedFellerHeatRate L D * δ) * ((n + 1 : ℕ) : ℝ) ^ 2))) :=
  ((reflectedFeller_gaussian_weight_summable _
    (mul_pos (reflectedFellerHeatRate_pos L hL D hD) hδ) 2).mul_left _).comp_injective Nat.succ_injective

end TimeTraps.Probability

end
