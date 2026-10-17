module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! Exact exponential tail identities. Translation uses the genuine
measure-preserving real translation, and the constant tail is evaluated
by the improper exponential integral. -/

namespace TimeTraps.Probability

open Set MeasureTheory

theorem graphPointDiscount_tail_translate (α t : ℝ) (U : ℝ → ℝ) :
    (∫ H in Ioi t, Real.exp (-(α * H)) * U (H - t)) =
      Real.exp (-(α * t)) * ∫ s in Ioi (0 : ℝ), Real.exp (-(α * s)) * U s := by
  have hp : (fun s : ℝ => s + t) ⁻¹' Ioi t = Ioi (0 : ℝ) := by
    ext s
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have he := (measurePreserving_add_right volume t).setIntegral_preimage_emb
    (MeasurableEquiv.addRight t).measurableEmbedding
    (fun H => Real.exp (-(α * H)) * U (H - t)) (Ioi t)
  rw [hp] at he
  rw [← he, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  dsimp only
  rw [add_sub_cancel_right, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem graphPointDiscount_tail_constant {α : ℝ} (hα : 0 < α) (t c : ℝ) :
    α * (∫ H in Ioi t, Real.exp (-(α * H)) * c) = Real.exp (-(α * t)) * c := by
  have he : (∫ H in Ioi t, Real.exp (-(α * H))) = Real.exp (-(α * t)) / α := by
    simpa only [neg_mul, neg_div_neg_eq] using
      integral_exp_mul_Ioi (a := -α) (neg_lt_zero.mpr hα) t
  rw [integral_mul_const, he]
  field_simp

end TimeTraps.Probability
