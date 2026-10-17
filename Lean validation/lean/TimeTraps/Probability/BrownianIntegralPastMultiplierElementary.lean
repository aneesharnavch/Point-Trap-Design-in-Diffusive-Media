module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierL2
public import TimeTraps.Probability.BrownianIntegralTruncationSpaces

@[expose] public section

/-! A bounded variable known at time s can multiply an actual elementary
integrand starting at or after s. Its canonical stochastic integral is
the product of that variable and the original elementary integral. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable {Z : Ω → ℝ} {M : ℝ≥0} {s : ℝ≥0}

def BrownianIntegralElementary.pastProduct (a : BrownianIntegralElementary B hBm P)
    (hs : s ≤ a.left) (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) : BrownianIntegralElementary B hBm P where
  left := a.left
  right := a.right
  ordered := a.ordered
  coefficient := fun ω => Z ω * a.coefficient ω
  adapted := (hZ.mono ((brownianNaturalFiltration B hBm).mono hs)).mul a.adapted
  squareIntegrable := by
    apply a.squareIntegrable.of_le_mul (c := M.val)
      ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).aestronglyMeasurable.mul
        a.squareIntegrable.aestronglyMeasurable)
    filter_upwards [] with ω
    change ‖Z ω * a.coefficient ω‖ ≤ M.val * ‖a.coefficient ω‖
    rw [norm_mul, Real.norm_eq_abs (Z ω)]
    exact mul_le_mul_of_nonneg_right (hb ω) (norm_nonneg _)

theorem brownianPastMultiplier_elementary_process (a : BrownianIntegralElementary B hBm P)
    (hs : s ≤ a.left) (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (p : ℝ × Ω) :
    brownianElementaryProcess (a.pastProduct hs hZ hb).left (a.pastProduct hs hZ hb).right
      (a.pastProduct hs hZ hb).coefficient p =
      Z p.2 * brownianElementaryProcess a.left a.right a.coefficient p := by
  change brownianIntervalIndicator a.left a.right p.1 * (Z p.2 * a.coefficient p.2) =
    Z p.2 * (brownianIntervalIndicator a.left a.right p.1 * a.coefficient p.2)
  ring

theorem brownianPastMultiplier_elementary (a : BrownianIntegralElementary B hBm P)
    (hs : s ≤ a.left) (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) :
    brownianPastMultiplierL2
      ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
      (fun p : ℝ × Ω => hb p.2) a.processL2 = (a.pastProduct hs hZ hb).processL2 := by
  apply Lp.ext
  filter_upwards [brownianPastMultiplierL2_coe
    ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
    (fun p : ℝ × Ω => hb p.2) a.processL2, a.processL2_coe,
    (a.pastProduct hs hZ hb).processL2_coe] with p hm ha hp
  rw [hm, ha, hp, brownianPastMultiplier_elementary_process]
  rfl

theorem brownianPastMultiplier_elementary_integral (hB : IsPreBrownianReal B P)
    (a : BrownianIntegralElementary B hBm P) (hs : s ≤ a.left)
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) :
    (a.pastProduct hs hZ hb).integralL2 hB =
      brownianPastMultiplierL2 (hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable hb
        (a.integralL2 hB) := by
  apply Lp.ext
  filter_upwards [(a.pastProduct hs hZ hb).integralL2_coe hB,
    brownianPastMultiplierL2_coe
      (hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable hb (a.integralL2 hB),
    a.integralL2_coe hB] with ω hp hm ha
  rw [hp, hm, ha]
  change (Z ω * a.coefficient ω) * (B a.right ω - B a.left ω) = _
  ring

end TimeTraps.Probability

end
