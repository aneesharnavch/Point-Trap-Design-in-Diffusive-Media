module

public import TimeTraps.Analysis.GraphConservativeMomentData

@[expose] public section

/-! Actual graph semigroup moment estimates from the full generator.
The fourth bound uses a generator controlled by the squared increment,
then integrates the proved second bound; it is quadratic in time. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedFeller_generator_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (q g : C(GraphRealization P.geometry, ℝ))
    (hqg : (graphConservativeContinuousStateL P.geometry q,
      -graphConservativeContinuousStateL P.geometry g) ∈ P.operator.graph)
    {C : ℝ} (hg : ∀ z, g z ≤ C) (x : GraphRealization P.geometry) (hx : q x = 0) (T : ℝ≥0) :
    P.realizedFeller T q x ≤ C * T.val := by
  have he := P.realizedFeller_diffusion_variation_apply q g hqg T x
  rw [hx, sub_zero] at he
  calc
    _ = ∫ s in (0 : ℝ)..T.val, P.realizedFeller s.toNNReal g x := he
    _ ≤ ∫ _s in (0 : ℝ)..T.val, C := intervalIntegral.integral_mono_on T.coe_nonneg
      ((P.realizedFeller_observation_continuous g x).intervalIntegrable 0 T.val)
      (intervalIntegrable_const) (fun s _ => P.realizedFeller_le_const hκ s.toNNReal hg x)
    _ = _ := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

theorem GraphShiftedContactOperatorProblem.realizedFeller_generator_quadratic_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (q₂ q₄ g₂ g₄ : C(GraphRealization P.geometry, ℝ))
    (h₂ : (graphConservativeContinuousStateL P.geometry q₂,
      -graphConservativeContinuousStateL P.geometry g₂) ∈ P.operator.graph)
    (h₄ : (graphConservativeContinuousStateL P.geometry q₄,
      -graphConservativeContinuousStateL P.geometry g₄) ∈ P.operator.graph)
    {C₂ C₄ : ℝ} (hC₄ : 0 ≤ C₄) (hg₂ : ∀ z, g₂ z ≤ C₂)
    (hg₄ : ∀ z, g₄ z ≤ C₄ * q₂ z)
    (x : GraphRealization P.geometry) (hx₂ : q₂ x = 0) (hx₄ : q₄ x = 0) (T : ℝ≥0) :
    P.realizedFeller T q₄ x ≤ C₂ * C₄ * T.val ^ 2 / 2 := by
  have he := P.realizedFeller_diffusion_variation_apply q₄ g₄ h₄ T x
  rw [hx₄, sub_zero] at he
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T.val) :
      P.realizedFeller s.toNNReal g₄ x ≤ C₄ * (C₂ * s) := by
    have hm := P.realizedFeller_mono s.toNNReal (g := C₄ • q₂) hg₄ x
    have hv : P.realizedFeller s.toNNReal (C₄ • q₂) x = C₄ * P.realizedFeller s.toNNReal q₂ x := by
      rw [map_smul]
      rfl
    have hq := P.realizedFeller_generator_bound hκ q₂ g₂ h₂ hg₂ x hx₂ s.toNNReal
    have ht : s.toNNReal.val = s := Real.coe_toNNReal s hs.1
    calc
      _ ≤ P.realizedFeller s.toNNReal (C₄ • q₂) x := hm
      _ = C₄ * P.realizedFeller s.toNNReal q₂ x := hv
      _ ≤ C₄ * (C₂ * s.toNNReal.val) := mul_le_mul_of_nonneg_left hq hC₄
      _ = _ := congrArg (fun r : ℝ => C₄ * (C₂ * r)) ht
  calc
    _ = ∫ s in (0 : ℝ)..T.val, P.realizedFeller s.toNNReal g₄ x := he
    _ ≤ ∫ s in (0 : ℝ)..T.val, C₄ * (C₂ * s) := intervalIntegral.integral_mono_on T.coe_nonneg
      ((P.realizedFeller_observation_continuous g₄ x).intervalIntegrable 0 T.val)
      (((continuous_const.mul (continuous_const.mul continuous_id)).intervalIntegrable 0 T.val)) hb
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id]
      ring

end TimeTraps.Analysis
