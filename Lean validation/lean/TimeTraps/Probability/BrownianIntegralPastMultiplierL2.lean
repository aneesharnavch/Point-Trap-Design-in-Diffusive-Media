module

public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplier
public import Mathlib.MeasureTheory.Function.Holder

@[expose] public section

/-! Bounded random multiplication on outcome L². Hölder multiplication
by the actual L∞ class gives a continuous linear operator; its values
agree almost everywhere with multiplication of representatives. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {Z : Ω → ℝ} {M : ℝ≥0}

def brownianPastMultiplierLInf (hZ : Measurable Z) (hb : ∀ ω, |Z ω| ≤ M.val) : Lp ℝ ∞ P :=
  (memLp_top_of_bound hZ.aestronglyMeasurable M.val
    (Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb ω))).toLp Z

theorem brownianPastMultiplierLInf_coe (hZ : Measurable Z) (hb : ∀ ω, |Z ω| ≤ M.val) :
    brownianPastMultiplierLInf (P := P) hZ hb =ᵐ[P] Z :=
  (memLp_top_of_bound hZ.aestronglyMeasurable M.val
    (Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb ω))).coeFn_toLp

def brownianPastMultiplierL2 (hZ : Measurable Z) (hb : ∀ ω, |Z ω| ≤ M.val) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL P ∞ 2 2 (brownianPastMultiplierLInf hZ hb)

theorem brownianPastMultiplierL2_coe (hZ : Measurable Z) (hb : ∀ ω, |Z ω| ≤ M.val)
    (f : Lp ℝ 2 P) : brownianPastMultiplierL2 hZ hb f =ᵐ[P] (fun ω => Z ω * f ω) := by
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
    (brownianPastMultiplierLInf (P := P) hZ hb) f
  filter_upwards [hh, brownianPastMultiplierLInf_coe (P := P) hZ hb] with ω hh hZω
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (brownianPastMultiplierLInf hZ hb) f) ω = _
  rw [hh, hZω]
  rfl

theorem brownianPastMultiplierL2_norm (hZ : Measurable Z) (hb : ∀ ω, |Z ω| ≤ M.val)
    (f : Lp ℝ 2 P) : ‖brownianPastMultiplierL2 hZ hb f‖ ≤ M.val * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [brownianPastMultiplierL2_coe hZ hb f] with ω hω
  rw [hω, norm_mul, Real.norm_eq_abs (Z ω)]
  exact mul_le_mul_of_nonneg_right (hb ω) (norm_nonneg _)

end TimeTraps.Probability

end
