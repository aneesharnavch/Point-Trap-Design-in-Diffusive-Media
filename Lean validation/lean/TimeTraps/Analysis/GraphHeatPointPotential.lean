module

public import TimeTraps.Analysis.GraphHeatPointPotentialKernel
public import TimeTraps.Analysis.GraphHeatPointPotentialTime
public import TimeTraps.Analysis.GraphHeatPointPotentialEnvelope

@[expose] public section

/-! Actual graph point potentials are finite and vanish uniformly at
short times. Integrability is proved before evaluating the ordinary time
integral; all closed-edge points, including graph vertices, are covered. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter Topology
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.heatPointPotential
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, P.heatPointKernelTime e d x y t

theorem GraphShiftedContactOperatorProblem.heatPointPotential_short_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T → T ≤ 1 →
      ∀ (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
        (y : Icc (0 : ℝ) (P.geometry.length d)),
        IntervalIntegrable (P.heatPointKernelTime e d x y) volume 0 T ∧
        0 ≤ P.heatPointPotential e d x y T ∧
        P.heatPointPotential e d x y T ≤ C * (T + 2 * Real.sqrt T) := by
  obtain ⟨C, hC, hb⟩ := P.heatKernel_short_bound
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 e d x y
  have hpoint (t : ℝ) (ht : t ∈ Ioc 0 T) :
      0 ≤ P.heatPointKernelTime e d x y t ∧
      P.heatPointKernelTime e d x y t ≤ C * (1 + 1 / Real.sqrt t) := by
    rw [P.heatPointKernelTime_of_pos e d x y ht.1]
    have h := hb t.toNNReal (Real.toNNReal_pos.mpr ht.1)
      (Real.toNNReal_le_iff_le_coe.mpr (ht.2.trans hT1)) e d x y
    simpa only [Real.coe_toNNReal t ht.1.le] using h
  have hm : AEStronglyMeasurable (P.heatPointKernelTime e d x y)
      (volume.restrict (Set.uIoc (0 : ℝ) T)) := by
    rw [uIoc_of_le hT]
    exact ((P.heatPointKernelTime_continuousOn e d x y).mono
      (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  have hi : IntervalIntegrable (P.heatPointKernelTime e d x y) volume 0 T := by
    apply (shortPointEnvelope_intervalIntegrable hT C).mono_fun' hm
    rw [uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hpoint t ht).1]
    exact (hpoint t ht).2
  refine ⟨hi, ?_, ?_⟩
  · unfold heatPointPotential
    rw [intervalIntegral.integral_of_le hT]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hpoint t ht).1
  · calc
      _ ≤ ∫ t in (0 : ℝ)..T, C * (1 + 1 / Real.sqrt t) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hT hi
          (shortPointEnvelope_intervalIntegrable hT C)
        intro t ht
        exact (hpoint t ⟨ht.1, ht.2.le⟩).2
      _ = _ := shortPointEnvelope_integral hT C

theorem GraphShiftedContactOperatorProblem.heatPointPotential_uniform_small
    (P : GraphShiftedContactOperatorProblem V E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (T : ℝ), 0 ≤ T → T ≤ δ →
      ∀ (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
        (y : Icc (0 : ℝ) (P.geometry.length d)),
        IntervalIntegrable (P.heatPointKernelTime e d x y) volume 0 T ∧
        0 ≤ P.heatPointPotential e d x y T ∧ P.heatPointPotential e d x y T < ε := by
  obtain ⟨C, hC, hb⟩ := P.heatPointPotential_short_bound
  have hc : Continuous (fun T : ℝ => C * (T + 2 * Real.sqrt T)) :=
    continuous_const.mul (continuous_id.add (continuous_const.mul Real.continuous_sqrt))
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) ε hε
  refine ⟨min 1 (δ / 2), by positivity, ?_⟩
  intro T hT hTδ e d x y
  have hT1 : T ≤ 1 := hTδ.trans (min_le_left _ _)
  have hnear : dist T 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hT]
    have hh := hTδ.trans (min_le_right _ _)
    linarith
  have hc' := hclose hnear
  simp only [Real.sqrt_zero, mul_zero, add_zero, Real.dist_eq, sub_zero] at hc'
  obtain ⟨hi, hn, hbound⟩ := hb T hT hT1 e d x y
  exact ⟨hi, hn, hbound.trans_lt ((abs_lt.mp hc').2)⟩

end TimeTraps.Analysis
