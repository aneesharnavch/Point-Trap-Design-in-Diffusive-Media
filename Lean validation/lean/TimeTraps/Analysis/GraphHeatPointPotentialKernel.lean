module

public import TimeTraps.Analysis.GraphHeatPointPotentialTrace
public import TimeTraps.Analysis.GraphShiftedContactHeatKernel

@[expose] public section

/-! Uniform short-time bounds for the actual continuous graph heat
kernel. The Riesz vectors are bounded by their proved evaluation estimate,
and the literal half-time inner product supplies the kernel bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.heatKernelVector_short_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t), t ≤ 1 →
      ∀ (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)),
        ‖P.heatKernelVector t ht e x‖ ^ 2 ≤ C * (1 + 1 / Real.sqrt (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := P.heatPointEvaluation_short_bound
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 e x
  have h := hb t ht ht1 e x (P.heatKernelVector t ht e x)
  rw [← P.heatKernelVector_inner, real_inner_self_eq_norm_sq] at h
  have hk : 0 < C * (1 + 1 / Real.sqrt (t : ℝ)) := by positivity
  have hn := sq_nonneg ‖P.heatKernelVector t ht e x‖
  nlinarith

theorem GraphShiftedContactOperatorProblem.heatKernel_short_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t), t ≤ 1 →
      ∀ (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
        (y : Icc (0 : ℝ) (P.geometry.length d)),
        0 ≤ P.heatKernel t ht e x d y ∧
          P.heatKernel t ht e x d y ≤ C * (1 + 1 / Real.sqrt (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := P.heatKernelVector_short_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro t ht ht1 e d x y
  refine ⟨P.heatKernel_nonneg t ht e d x y, ?_⟩
  have hh : (t / 2 : ℝ≥0) ≤ 1 := by calc
    t / 2 ≤ t := div_le_self (show 0 ≤ t from zero_le) (by norm_num)
    _ ≤ 1 := ht1
  have hx := hb (t / 2) (div_pos ht (by norm_num)) hh e x
  have hy := hb (t / 2) (div_pos ht (by norm_num)) hh d y
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 ht
  have hhalf : 0 < Real.sqrt ((t : ℝ) / 2) := Real.sqrt_pos.2 (by positivity)
  have he : 1 / Real.sqrt ((t : ℝ) / 2) ≤ 2 / Real.sqrt (t : ℝ) := by
    apply (div_le_div_iff₀ hhalf hs).2
    have h1 := Real.sq_sqrt (show 0 ≤ (t : ℝ) from t.property)
    have h2 := Real.sq_sqrt (show 0 ≤ (t : ℝ) / 2 from by positivity)
    nlinarith
  rw [P.heatKernel_eq_inner]
  calc
    _ ≤ ‖P.heatKernelVector (t / 2) _ e x‖ * ‖P.heatKernelVector (t / 2) _ d y‖ :=
      real_inner_le_norm _ _
    _ ≤ C * (1 + 1 / Real.sqrt ((t : ℝ) / 2)) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat] at hx hy
      nlinarith [sq_nonneg (‖P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x‖ -
        ‖P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) d y‖)]
    _ ≤ (2 * C) * (1 + 1 / Real.sqrt (t : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left he hC.le
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith

end TimeTraps.Analysis
