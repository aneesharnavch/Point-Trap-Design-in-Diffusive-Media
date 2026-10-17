module

public import TimeTraps.Probability.BrownianTanakaSmoothOccupation

@[expose] public section

/-! Away from its level, the actual smooth Tanaka kernel is quadratically
small in the smoothing scale. The resulting finite-time increment bound
uses the ordinary time integral and only joint measurability of the path. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

theorem tanakaOccupationKernel_away_bound {ε δ x : ℝ}
    (hδ : 0 < δ) (hx : δ ≤ |x|) :
    tanakaOccupationKernel ε x ≤ ε ^ 2 / (2 * δ ^ 3) := by
  have hbase : δ ≤ tanakaSmoothAbs ε x := hx.trans (abs_le_tanakaSmoothAbs ε x)
  unfold tanakaOccupationKernel
  apply div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hbase 3) (by norm_num)

theorem brownianTanakaKernelDrift_increment
    {ε : ℝ} (hε : 0 < ε)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (a : ℝ) (S T : ℝ≥0) (ω : Ω) :
    brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - a)) T ω -
      brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - a)) S ω =
      ∫ s in S.val..T.val, tanakaOccupationKernel ε (B s.toNNReal ω - a) := by
  have hi (t : ℝ≥0) := brownianItoDrift_bounded_intervalIntegrable
    (g := fun x => tanakaOccupationKernel ε (x - a))
    ((tanakaOccupationKernel_continuous hε).measurable.comp (measurable_id.sub_const a))
    hjoint (fun x => by
      rw [abs_of_nonneg (tanakaOccupationKernel_nonneg hε (x - a))]
      exact tanakaOccupationKernel_uniform_bound hε (x - a)) t ω
  exact intervalIntegral.integral_interval_sub_left (hi T) (hi S)

theorem brownianTanakaKernelDrift_increment_away_bound
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (a : ℝ) {S T : ℝ≥0} (hST : S ≤ T) (ω : Ω)
    (haway : ∀ s ∈ Icc S T, δ ≤ |B s ω - a|) :
    |brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - a)) T ω -
      brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - a)) S ω| ≤
      (ε ^ 2 / (2 * δ ^ 3)) * (T.val - S.val) := by
  rw [brownianTanakaKernelDrift_increment hε hjoint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := S.val) (b := T.val)
    (f := fun s => tanakaOccupationKernel ε (B s.toNNReal ω - a))
    (C := ε ^ 2 / (2 * δ ^ 3)) (fun s hs => by
      rw [uIoc_of_le (show S.val ≤ T.val from hST)] at hs
      have hs₀ : 0 ≤ s := S.property.trans hs.1.le
      have hst : s.toNNReal ∈ Icc S T := by
        constructor
        · change S.val ≤ (s.toNNReal : ℝ)
          rw [Real.coe_toNNReal _ hs₀]
          exact hs.1.le
        · change (s.toNNReal : ℝ) ≤ T.val
          rw [Real.coe_toNNReal _ hs₀]
          exact hs.2
      rw [Real.norm_eq_abs, abs_of_nonneg (tanakaOccupationKernel_nonneg hε _)]
      exact tanakaOccupationKernel_away_bound hδ (haway _ hst))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (show S.val ≤ T.val from hST))] using hb

end TimeTraps.Probability
