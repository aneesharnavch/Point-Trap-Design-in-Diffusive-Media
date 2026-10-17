module

public import TimeTraps.Interval.WeightedGridDerivative

@[expose] public section

/-! Second-order weighted-grid calculus under continuity of the weight.
The residual of one interior node depends only on that node and its two
neighbors. No global convexity is inferred for an arbitrary positive weight. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter
open scoped Topology

noncomputable def weightedGridResidual (W : CellWeight) (a q b : ℝ) : ℝ :=
  ∫ z in (a + q) / 2..(q + b) / 2, W.value z * (q - z)

noncomputable def weightedGridHessianEdge (W : CellWeight) (a b : ℝ) : ℝ :=
  -(W.value ((a + b) / 2) * (b - a)) / 2

noncomputable def weightedGridHessianDiagonal (W : CellWeight) (a q b : ℝ) : ℝ :=
  2 * (W.primitive ((q + b) / 2) - W.primitive ((a + q) / 2)) +
    weightedGridHessianEdge W a q + weightedGridHessianEdge W q b

theorem weightedGridResidual_formula (W : CellWeight) {a q b : ℝ}
    (hl : (a + q) / 2 ∈ Icc (0 : ℝ) 1) (hr : (q + b) / 2 ∈ Icc (0 : ℝ) 1) :
    weightedGridResidual W a q b =
      q * (W.primitive ((q + b) / 2) - W.primitive ((a + q) / 2)) -
        (W.moment ((q + b) / 2) - W.moment ((a + q) / 2)) :=
  weightedGridResidual_primitive W q hl hr

theorem weightedGridHessianDiagonal_integral (W : CellWeight) {a q b : ℝ}
    (hl : (a + q) / 2 ∈ Icc (0 : ℝ) 1) (hr : (q + b) / 2 ∈ Icc (0 : ℝ) 1) :
    weightedGridHessianDiagonal W a q b =
      2 * (∫ z in (a + q) / 2..(q + b) / 2, W.value z) -
        (W.value ((a + q) / 2) * (q - a) + W.value ((q + b) / 2) * (b - q)) / 2 := by
  rw [W.integral_eq_primitive hl hr]
  unfold weightedGridHessianDiagonal weightedGridHessianEdge
  ring

theorem weightedGridResidual_derivative (W : CellWeight) {a q b : ℝ → ℝ} {a' q' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hq : HasDerivAt q q' t) (hb : HasDerivAt b b' t)
    (hl : (a t + q t) / 2 ∈ Ioo (0 : ℝ) 1)
    (hr : (q t + b t) / 2 ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => weightedGridResidual W (a s) (q s) (b s))
      ((weightedGridHessianEdge W (a t) (q t) * a' +
          weightedGridHessianDiagonal W (a t) (q t) (b t) * q' +
          weightedGridHessianEdge W (q t) (b t) * b') / 2) t := by
  have hml := (ha.add hq).div_const 2
  have hmr := (hq.add hb).div_const 2
  have hpl := (W.primitive_derivative hl).comp t hml
  have hpr := (W.primitive_derivative hr).comp t hmr
  have hMl := (W.moment_derivative hl).comp t hml
  have hMr := (W.moment_derivative hr).comp t hmr
  have hd₀ := (hq.mul (hpr.sub hpl)).sub (hMr.sub hMl)
  have hd : HasDerivAt
      (fun s => q s * (W.primitive ((q s + b s) / 2) - W.primitive ((a s + q s) / 2)) -
        (W.moment ((q s + b s) / 2) - W.moment ((a s + q s) / 2)))
      ((weightedGridHessianEdge W (a t) (q t) * a' +
          weightedGridHessianDiagonal W (a t) (q t) (b t) * q' +
          weightedGridHessianEdge W (q t) (b t) * b') / 2) t := by
    convert! hd₀ using 1
    dsimp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply,
      weightedGridHessianDiagonal, weightedGridHessianEdge]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [hml.continuousAt.eventually (Ioo_mem_nhds hl.1 hl.2),
    hmr.continuousAt.eventually (Ioo_mem_nhds hr.1 hr.2)] with s hs₁ hs₂
  exact weightedGridResidual_formula W (Ioo_subset_Icc_self hs₁) (Ioo_subset_Icc_self hs₂)

theorem weightedGridGradientCell_derivative (W : CellWeight) {a q b : ℝ → ℝ} {a' q' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hq : HasDerivAt q q' t) (hb : HasDerivAt b b' t)
    (hl : (a t + q t) / 2 ∈ Ioo (0 : ℝ) 1)
    (hr : (q t + b t) / 2 ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => 2 * weightedGridResidual W (a s) (q s) (b s))
      (weightedGridHessianEdge W (a t) (q t) * a' +
        weightedGridHessianDiagonal W (a t) (q t) (b t) * q' +
        weightedGridHessianEdge W (q t) (b t) * b') t := by
  have h := (weightedGridResidual_derivative W ha hq hb hl hr).const_mul 2
  exact h.congr_deriv (by ring)

theorem weightedGridHessianEdge_neg (W : CellWeight) {a b : ℝ}
    (hab : a < b) (hm : (a + b) / 2 ∈ Icc (0 : ℝ) 1) :
    weightedGridHessianEdge W a b < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (W.positive _ hm) (sub_pos.mpr hab))) (by norm_num)

theorem weightedGridHessianEdge_constant (W : CellWeight) (Ω : ℝ)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω) {a b : ℝ}
    (hm : (a + b) / 2 ∈ Icc (0 : ℝ) 1) :
    weightedGridHessianEdge W a b = -Ω * (b - a) / 2 := by
  rw [weightedGridHessianEdge, hW _ hm]
  ring

theorem weightedGridHessianDiagonal_constant (W : CellWeight) (Ω : ℝ)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω) {a q b : ℝ}
    (hl : (a + q) / 2 ∈ Icc (0 : ℝ) 1) (hr : (q + b) / 2 ∈ Icc (0 : ℝ) 1) :
    weightedGridHessianDiagonal W a q b = Ω * (b - a) / 2 := by
  have hi : (∫ z in (a + q) / 2..(q + b) / 2, W.value z) = Ω * ((q + b) / 2 - (a + q) / 2) := by
    calc
      _ = ∫ _ in (a + q) / 2..(q + b) / 2, Ω := by
        apply intervalIntegral.integral_congr
        intro z hz
        exact hW z ⟨(le_min hl.1 hr.1).trans hz.1, hz.2.trans (max_le hl.2 hr.2)⟩
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  rw [weightedGridHessianDiagonal_integral W hl hr, hi, hW _ hl, hW _ hr]
  ring

end TimeTraps.Interval
