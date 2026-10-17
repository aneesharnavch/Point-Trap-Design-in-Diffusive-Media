module

public import TimeTraps.Interval.WeightedGridIFTPrimitive
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The actual centroid residual for the affine weight perturbation, in
free interior coordinates. Its primitive expression makes joint C²
regularity transparent without extending h beyond the unit interval. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter
open scoped ContDiff Topology

variable {n : ℕ}

noncomputable def gridIFTBaseline (n : ℕ) (i : Fin n) : ℝ :=
  ((i.val : ℝ) + 1) / ((n : ℝ) + 1)

noncomputable def gridIFTLeft (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  (cdfNode q i.castSucc.castSucc + q i) / 2

noncomputable def gridIFTRight (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  (q i + cdfNode q i.succ.succ) / 2

noncomputable def gridIFTResidual (h : ℝ → ℝ) (Ω : ℝ) (v : ℝ × (Fin n → ℝ)) (i : Fin n) : ℝ :=
  Ω * (v.2 i * (gridIFTRight v.2 i - gridIFTLeft v.2 i) -
    ((gridIFTRight v.2 i) ^ 2 - (gridIFTLeft v.2 i) ^ 2) / 2 +
    v.1 * (v.2 i * (gridIFTPrimitive h (gridIFTRight v.2 i) - gridIFTPrimitive h (gridIFTLeft v.2 i)) -
      (gridIFTMoment h (gridIFTRight v.2 i) - gridIFTMoment h (gridIFTLeft v.2 i))))

theorem gridIFTNode_contDiff (v : Fin (n + 2)) :
    ContDiff ℝ 2 (fun q : Fin n → ℝ => cdfNode q v) := by
  refine Fin.cases ?_ (fun k => ?_) v
  · simpa only [cdfNode_first] using (contDiff_const : ContDiff ℝ 2 (fun _ : Fin n → ℝ => (0 : ℝ)))
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change ContDiff ℝ 2 (fun q : Fin n → ℝ => cdfNode q (Fin.last (n + 1)))
      simpa only [cdfNode_last] using (contDiff_const : ContDiff ℝ 2 (fun _ : Fin n → ℝ => (1 : ℝ)))
    · simp only [cdfNode_site]
      fun_prop

theorem gridIFTLeft_contDiff (i : Fin n) : ContDiff ℝ 2 (fun q : Fin n → ℝ => gridIFTLeft q i) :=
  ((gridIFTNode_contDiff i.castSucc.castSucc).add (by fun_prop)).div_const 2

theorem gridIFTRight_contDiff (i : Fin n) : ContDiff ℝ 2 (fun q : Fin n → ℝ => gridIFTRight q i) :=
  ((by fun_prop : ContDiff ℝ 2 (fun q : Fin n → ℝ => q i)).add
    (gridIFTNode_contDiff i.succ.succ)).div_const 2

theorem gridIFTResidual_contDiffAt (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1))
    (Ω : ℝ) (v : ℝ × (Fin n → ℝ))
    (hin : ∀ i, gridIFTLeft v.2 i ∈ Ioo (0 : ℝ) 1 ∧ gridIFTRight v.2 i ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (gridIFTResidual h Ω) v := by
  apply contDiffAt_pi.mpr
  intro i
  have hl : ContDiffAt ℝ 2 (fun w : ℝ × (Fin n → ℝ) => gridIFTLeft w.2 i) v :=
    (gridIFTLeft_contDiff i).contDiffAt.comp v contDiffAt_snd
  have hr : ContDiffAt ℝ 2 (fun w : ℝ × (Fin n → ℝ) => gridIFTRight w.2 i) v :=
    (gridIFTRight_contDiff i).contDiffAt.comp v contDiffAt_snd
  have hpl := ((gridIFTPrimitive_contDiff h hh).contDiffAt (Ioo_mem_nhds (hin i).1.1 (hin i).1.2)).comp v hl
  have hpr := ((gridIFTPrimitive_contDiff h hh).contDiffAt (Ioo_mem_nhds (hin i).2.1 (hin i).2.2)).comp v hr
  have hMl := ((gridIFTMoment_contDiff h hh).contDiffAt (Ioo_mem_nhds (hin i).1.1 (hin i).1.2)).comp v hl
  have hMr := ((gridIFTMoment_contDiff h hh).contDiffAt (Ioo_mem_nhds (hin i).2.1 (hin i).2.2)).comp v hr
  have hq : ContDiffAt ℝ 2 (fun w : ℝ × (Fin n → ℝ) => w.2 i) v := by fun_prop
  exact contDiffAt_const.mul (((hq.mul (hr.sub hl)).sub (((hr.pow 2).sub (hl.pow 2)).div_const 2)).add
    (contDiffAt_fst.mul ((hq.mul (hpr.sub hpl)).sub (hMr.sub hMl))))

theorem gridIFTResidual_eq_integral (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    (Ω ε : ℝ) (q : Fin n → ℝ) (i : Fin n)
    (hl : gridIFTLeft q i ∈ Icc (0 : ℝ) 1) (hr : gridIFTRight q i ∈ Icc (0 : ℝ) 1) :
    gridIFTResidual h Ω (ε, q) i =
      ∫ z in gridIFTLeft q i..gridIFTRight q i, Ω * (1 + ε * h z) * (q i - z) := by
  let a := gridIFTLeft q i
  let b := gridIFTRight q i
  have hc : IntervalIntegrable (fun z => q i - z) volume a b :=
    (continuous_const.sub continuous_id).intervalIntegrable a b
  have hhq : IntervalIntegrable (fun z => h z * (q i - z)) volume a b :=
    ((hh.mul (continuousOn_const.sub continuousOn_id)).mono (uIcc_subset_Icc hl hr)).intervalIntegrable
  have hconst : (∫ z in a..b, q i - z) = q i * (b - a) - (b ^ 2 - a ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => q i) (g := fun z : ℝ => z)
        intervalIntegrable_const (continuous_id.intervalIntegrable a b),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  symm
  calc
    _ = Ω * ((∫ z in a..b, q i - z) + ε * ∫ z in a..b, h z * (q i - z)) := by
      have he : (fun z => Ω * (1 + ε * h z) * (q i - z)) =
          fun z => Ω * ((q i - z) + ε * (h z * (q i - z))) := by funext z; ring
      rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hc (hhq.const_mul ε),
        intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [hconst, gridIFT_residual_integral h hh (q i) hl hr]
      rfl

theorem gridIFTBaseline_nodes :
    cdfNode (gridIFTBaseline n) = (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).point := by
  funext v
  refine Fin.cases ?_ (fun k => ?_) v
  · rw [cdfNode_first, StrictPartition.first]
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change cdfNode (gridIFTBaseline n) (Fin.last (n + 1)) =
        (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).point (Fin.last (n + 1))
      rw [cdfNode_last, StrictPartition.last]
    · rw [cdfNode_site]
      simp only [gridIFTBaseline, StrictPartition.uniform, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]

theorem gridIFTBaseline_midpoints (i : Fin n) :
    gridIFTLeft (gridIFTBaseline n) i ∈ Ioo (0 : ℝ) 1 ∧
      gridIFTRight (gridIFTBaseline n) i ∈ Ioo (0 : ℝ) 1 := by
  let Q := StrictPartition.uniform (n + 1) (Nat.succ_pos n)
  have hq : gridIFTBaseline n i = Q.point i.castSucc.succ := by
    rw [← gridIFTBaseline_nodes, cdfNode_site]
  constructor
  · rw [gridIFTLeft, gridIFTBaseline_nodes, hq]
    exact Q.closed.canonicalMidpoint_interior Q.strictMono i.castSucc
  · rw [gridIFTRight, gridIFTBaseline_nodes, hq]
    have hm := Q.closed.canonicalMidpoint_interior Q.strictMono i.succ
    change (Q.point i.succ.castSucc + Q.point i.succ.succ) / 2 ∈ Ioo (0 : ℝ) 1 at hm
    simpa only [Fin.castSucc_succ] using hm

theorem gridIFTResidual_baseline (h : ℝ → ℝ) (Ω : ℝ) :
    gridIFTResidual h Ω (0, gridIFTBaseline n) = 0 := by
  funext i
  simp only [gridIFTResidual, zero_mul, add_zero, gridIFTLeft, gridIFTRight, gridIFTBaseline_nodes]
  simp only [gridIFTBaseline, StrictPartition.uniform, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
    Pi.zero_apply]
  ring

theorem gridIFTResidual_epsilon_derivative (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    (Ω ε : ℝ) (q : Fin n → ℝ) (i : Fin n)
    (hl : gridIFTLeft q i ∈ Icc (0 : ℝ) 1) (hr : gridIFTRight q i ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun e => gridIFTResidual h Ω (e, q) i)
      (Ω * ∫ z in gridIFTLeft q i..gridIFTRight q i, h z * (q i - z)) ε := by
  rw [gridIFT_residual_integral h hh (q i) hl hr]
  have hd := (((hasDerivAt_id ε).mul_const
    (q i * (gridIFTPrimitive h (gridIFTRight q i) - gridIFTPrimitive h (gridIFTLeft q i)) -
      (gridIFTMoment h (gridIFTRight q i) - gridIFTMoment h (gridIFTLeft q i)))).const_add
      (q i * (gridIFTRight q i - gridIFTLeft q i) -
        ((gridIFTRight q i) ^ 2 - (gridIFTLeft q i) ^ 2) / 2)).const_mul Ω
  convert! hd using 1
  simp only [one_mul]

end TimeTraps.Interval
