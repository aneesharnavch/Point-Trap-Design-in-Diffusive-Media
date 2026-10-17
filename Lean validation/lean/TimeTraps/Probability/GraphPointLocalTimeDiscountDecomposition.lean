module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountMean
public import TimeTraps.Probability.GraphPointLocalTimeDiscountSplit

@[expose] public section

/-! The literal discounted terminal average splits into the raw local-time
prefix and the actual heat point resolvent evaluated at the current state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPrefix
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  Real.exp (-(α * (t : ℝ))) * P.pointLocalTime a t p +
    α * ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(α * s)) * P.pointLocalTime a s.toNNReal p

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedResolvent
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.pointLocalTimeDiscountedPrefix a α t p +
    Real.exp (-(α * (t : ℝ))) * P.pointLocalTimeDiscountedPotential a α (p t)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_real_horizon
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) {H : ℝ} (hH : 0 ≤ H) :
    P.pointLocalTimeTerminalProcess a H.toNNReal t p =
      P.pointLocalTime a (min (t : ℝ) H).toNNReal p +
        P.realizedHeatPointPotential (p t) a (H - min (t : ℝ) H) := by
  rcases le_total (t : ℝ) H with htH | hHt
  · have hn : t ≤ H.toNNReal := by
      change (t : ℝ) ≤ (H.toNNReal : ℝ)
      rwa [Real.coe_toNNReal H hH]
    simp only [pointLocalTimeTerminalProcess, NNReal.val_eq_coe, min_eq_left hn, min_eq_left htH,
      Real.toNNReal_coe, Real.coe_toNNReal H hH]
  · have hn : H.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hHt
    simp only [pointLocalTimeTerminalProcess, NNReal.val_eq_coe, min_eq_right hn, min_eq_right hHt,
      Real.coe_toNNReal H hH, sub_self, realizedHeatPointPotential,
      intervalIntegral.integral_same, add_zero]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal_decomposition
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    P.pointLocalTimeDiscountedTerminal a α t =ᵐ[P.continuousPathLaw hκ x]
      P.pointLocalTimeDiscountedResolvent a α t := by
  let inst := P.continuousPathLaw_probability hκ x
  filter_upwards [(P.pointLocalTimeDiscountTerminal_product_integrable hκ x a hα t).prod_left_ae] with p hp
  let L : ℝ → ℝ := fun H => P.pointLocalTime a H.toNNReal p
  let U : ℝ → ℝ := fun H => P.realizedHeatPointPotential (p t) a H
  have he : (fun H => Real.exp (-(α * H)) * P.pointLocalTimeTerminalProcess a H.toNNReal t p)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun H => Real.exp (-(α * H)) * (L (min (t : ℝ) H) + U (H - min (t : ℝ) H))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    rw [P.pointLocalTimeTerminalProcess_real_horizon a t p hH.le]
  have hsplit := graphPointDiscount_terminal_split hα t.coe_nonneg L U
    (by simp only [U, realizedHeatPointPotential, intervalIntegral.integral_same]) (hp.congr he)
  change α * (∫ H in Ioi (0 : ℝ), Real.exp (-(α * H)) * P.pointLocalTimeTerminalProcess a H.toNNReal t p) = _
  rw [integral_congr_ae he, hsplit]
  simp only [L, U, Real.toNNReal_coe, pointLocalTimeDiscountedResolvent,
    pointLocalTimeDiscountedPrefix, pointLocalTimeDiscountedPotential]
  ring

end TimeTraps.Analysis
