module

public import TimeTraps.Analysis.GraphShiftedContactHeatKernel

@[expose] public section

/-! Time regularity of the actual graph point kernel. A positive anchor
time writes each nearby Riesz vector as the strongly continuous original
heat acting on one fixed vector. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph InnerProductSpace Filter Topology
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.heatKernelVector_time_continuous
    (P : GraphShiftedContactOperatorProblem V E)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    Continuous (fun t : {t : ℝ≥0 // 0 < t} => P.heatKernelVector t.val t.property e x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let s : ℝ≥0 := t.val / 2
  have hs : 0 < s := div_pos t.property (by norm_num)
  have hst : s < t.val := by dsimp [s]; exact half_lt_self t.property
  have hc : Continuous (fun r : {t : ℝ≥0 // 0 < t} =>
      P.heatSemigroup (r.val - s) (P.heatKernelVector s hs e x)) :=
    (P.heatSemigroup_strong_continuous _).comp (continuous_subtype_val.sub continuous_const)
  have he : (fun r : {t : ℝ≥0 // 0 < t} => P.heatKernelVector r.val r.property e x) =ᶠ[𝓝 t]
      (fun r => P.heatSemigroup (r.val - s) (P.heatKernelVector s hs e x)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds hst] with r hr
    have h := P.heatKernelVector_add s hs (r.val - s) e x
    simpa only [add_tsub_cancel_of_le hr.le] using h
  exact hc.continuousAt.congr_of_eventuallyEq he

theorem GraphShiftedContactOperatorProblem.heatKernel_time_continuous
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) :
    Continuous (fun t : {t : ℝ≥0 // 0 < t} => P.heatKernel t.val t.property e x d y) := by
  have hh : Continuous (fun t : {t : ℝ≥0 // 0 < t} =>
      (⟨t.val / 2, div_pos t.property (by norm_num)⟩ : {t : ℝ≥0 // 0 < t})) :=
    (continuous_subtype_val.div_const 2).subtype_mk _
  have hx := (P.heatKernelVector_time_continuous e x).comp hh
  have hy := (P.heatKernelVector_time_continuous d y).comp hh
  have hi : Continuous (fun t : {t : ℝ≥0 // 0 < t} =>
      inner ℝ (P.heatKernelVector (t.val / 2) (div_pos t.property (by norm_num)) e x)
        (P.heatKernelVector (t.val / 2) (div_pos t.property (by norm_num)) d y)) := hx.inner hy
  exact hi.congr (fun t => (P.heatKernel_eq_inner t.val t.property e d x y).symm)

noncomputable def GraphShiftedContactOperatorProblem.heatPointKernelTime
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) (t : ℝ) : ℝ :=
  if ht : 0 < t then P.heatKernel t.toNNReal (Real.toNNReal_pos.mpr ht) e x d y else 0

theorem GraphShiftedContactOperatorProblem.heatPointKernelTime_of_pos
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) {t : ℝ} (ht : 0 < t) :
    P.heatPointKernelTime e d x y t =
      P.heatKernel t.toNNReal (Real.toNNReal_pos.mpr ht) e x d y := dif_pos ht

theorem GraphShiftedContactOperatorProblem.heatPointKernelTime_continuousOn
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) :
    ContinuousOn (P.heatPointKernelTime e d x y) (Ioi 0) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc : Continuous (fun t : Ioi (0 : ℝ) =>
      (⟨t.val.toNNReal, Real.toNNReal_pos.mpr t.property⟩ : {t : ℝ≥0 // 0 < t})) :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  exact ((P.heatKernel_time_continuous e d x y).comp hc).congr
    (fun t => (P.heatPointKernelTime_of_pos e d x y t.property).symm)

end TimeTraps.Analysis
