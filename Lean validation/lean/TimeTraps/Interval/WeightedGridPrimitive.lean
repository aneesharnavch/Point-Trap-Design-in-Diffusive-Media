module

public import TimeTraps.Interval.WeightedGridCells

@[expose] public section

/-! Primitive calculus for moving nearest-grid cells. Continuity of the
positive weight suffices: the midpoint identity cancels every derivative
of a moving cell boundary, without differentiating the weight. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology

noncomputable def CellWeight.secondMoment (W : CellWeight) (x : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, W.value z * z ^ 2

noncomputable def weightedGridBoundary (W : CellWeight) (a b : ℝ) : ℝ :=
  weightedCDFPrimitive W a ((a + b) / 2) - weightedCDFPrimitive W b ((a + b) / 2)

theorem CellWeight.primitive_derivative (W : CellWeight) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt W.primitive (W.value x) x :=
  integral_primitive_hasDerivAt W.continuous hx

theorem CellWeight.moment_derivative (W : CellWeight) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt W.moment (W.value x * x) x :=
  integral_primitive_hasDerivAt (W.continuous.mul continuousOn_id) hx

theorem CellWeight.secondMoment_derivative (W : CellWeight) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt W.secondMoment (W.value x * x ^ 2) x :=
  integral_primitive_hasDerivAt (W.continuous.mul (continuousOn_id.pow 2)) hx

theorem weightedCDFPrimitive_zero (W : CellWeight) (q : ℝ) :
    weightedCDFPrimitive W q 0 = 0 := by
  simp only [weightedCDFPrimitive, intervalIntegral.integral_same]

theorem weightedCDFPrimitive_formula (W : CellWeight) (q : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    weightedCDFPrimitive W q x =
      q ^ 2 * W.primitive x - 2 * q * W.moment x + W.secondMoment x := by
  have hp := W.integrable (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩) hx
  have hm := W.moment_integrable (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩) hx
  have h₂ : IntervalIntegrable (fun z => W.value z * z ^ 2) volume 0 x :=
    ((W.continuous.mul (continuousOn_id.pow 2)).mono
      (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  symm
  calc
    _ = ∫ z in (0 : ℝ)..x, (q ^ 2 * W.value z - 2 * q * (W.value z * z) + W.value z * z ^ 2) := by
      rw [intervalIntegral.integral_add ((hp.const_mul _).sub (hm.const_mul _)) h₂,
        intervalIntegral.integral_sub (hp.const_mul _) (hm.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rfl
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z _
      ring

theorem weightedCDFPrimitive_derivative (W : CellWeight) {q x : ℝ → ℝ} {q' x' t : ℝ}
    (hq : HasDerivAt q q' t) (hx : HasDerivAt x x' t) (hin : x t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => weightedCDFPrimitive W (q s) (x s))
      (2 * q' * (q t * W.primitive (x t) - W.moment (x t)) +
        W.value (x t) * (q t - x t) ^ 2 * x') t := by
  have hp := (W.primitive_derivative hin).comp t hx
  have hm := (W.moment_derivative hin).comp t hx
  have h₂ := (W.secondMoment_derivative hin).comp t hx
  have hd₀ := (((hq.pow 2).mul hp).sub ((hq.const_mul 2).mul hm)).add h₂
  have hd : HasDerivAt
      (fun s => q s ^ 2 * W.primitive (x s) - 2 * q s * W.moment (x s) + W.secondMoment (x s))
      (2 * q' * (q t * W.primitive (x t) - W.moment (x t)) +
        W.value (x t) * (q t - x t) ^ 2 * x') t := by
    convert! hd₀ using 1
    dsimp only [Function.comp_apply, Pi.pow_apply]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [hx.continuousAt.eventually (Ioo_mem_nhds hin.1 hin.2)] with s hs
  exact weightedCDFPrimitive_formula W (q s) (Ioo_subset_Icc_self hs)

theorem weightedGridBoundary_formula (W : CellWeight) (a b : ℝ)
    (hm : (a + b) / 2 ∈ Icc (0 : ℝ) 1) :
    weightedGridBoundary W a b =
      (a ^ 2 - b ^ 2) * W.primitive ((a + b) / 2) -
        2 * (a - b) * W.moment ((a + b) / 2) := by
  rw [weightedGridBoundary, weightedCDFPrimitive_formula W a hm,
    weightedCDFPrimitive_formula W b hm]
  ring

theorem weightedGridBoundary_derivative (W : CellWeight) {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t)
    (hin : (a t + b t) / 2 ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => weightedGridBoundary W (a s) (b s))
      (2 * a' * (a t * W.primitive ((a t + b t) / 2) - W.moment ((a t + b t) / 2)) -
        2 * b' * (b t * W.primitive ((a t + b t) / 2) - W.moment ((a t + b t) / 2))) t := by
  have hm := (ha.add hb).div_const 2
  have hd := (weightedCDFPrimitive_derivative W ha hm hin).sub
    (weightedCDFPrimitive_derivative W hb hm hin)
  exact hd.congr_deriv (by dsimp only [Pi.add_apply]; ring)

theorem weightedGridResidual_primitive (W : CellWeight) (q : ℝ) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in a..b, W.value z * (q - z)) =
      q * (W.primitive b - W.primitive a) - (W.moment b - W.moment a) := by
  calc
    _ = ∫ z in a..b, (q * W.value z - W.value z * z) := by
      apply intervalIntegral.integral_congr
      intro z _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub ((W.integrable ha hb).const_mul q)
        (W.moment_integrable ha hb), intervalIntegral.integral_const_mul,
        W.integral_eq_primitive ha hb, W.integral_eq_moment ha hb]

end TimeTraps.Interval
