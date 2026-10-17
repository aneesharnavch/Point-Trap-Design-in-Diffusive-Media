module

public import TimeTraps.Probability.GraphAtomicSurvivalLoss
public import TimeTraps.Probability.GraphPhysicalClockPath

@[expose] public section

/-! The original Robin Dynkin expression along the actual graph path.
Its running clock uses the original per-edge rho. Continuity and an
integrable compact-path bound are derived before its martingale identity
is supplied by the weak-resolvent representation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.atomicCompensatedProcess
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (u : C(GraphRealization P.geometry, ℝ))
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  u (p t) + (P.geometry.physicalClock b hb t p : ℝ) -
    ∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p

noncomputable def GraphShiftedContactOperatorProblem.atomicCompensatedBound
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (u : C(GraphRealization P.geometry, ℝ))
    (T : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  ‖u‖ + (P.geometry.physicalSpeedUpper b hb : ℝ) * (T : ℝ) +
    ∑ i, |κ i * u (a i)| * P.pointLocalTime (a i) T p

theorem GraphShiftedContactOperatorProblem.atomicCompensatedProcess_continuous_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (u : C(GraphRealization P.geometry, ℝ)) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, Continuous (fun t => P.atomicCompensatedProcess b hb a κ u t p) := by
  filter_upwards [ae_all_iff.mpr (fun i => P.pointLocalTime_regular_ae h0 x (a i))] with p hp
  have hc := NNReal.continuous_coe.comp (P.geometry.physicalClock_continuous b hb p)
  have hs : Continuous (fun t => ∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p) :=
    continuous_finsetSum _ (fun i _ => ((hp i).1).const_mul (κ i * u (a i)))
  exact ((u.continuous.comp p.continuous).add hc).sub hs

theorem GraphShiftedContactOperatorProblem.atomicCompensatedBound_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (u : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    Integrable (P.atomicCompensatedBound b hb a κ u T) (P.continuousPathLaw h0 x) := by
  let _ := P.continuousPathLaw_probability h0 x
  exact (integrable_const _).add (integrable_finsetSum _ (fun i _ =>
    ((P.pointLocalTime_memLp h0 x (a i) T).integrable (by norm_num)).const_mul (|κ i * u (a i)|)))

theorem GraphShiftedContactOperatorProblem.atomicCompensatedProcess_bound_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (u : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, ∀ t ∈ Icc 0 T,
      |P.atomicCompensatedProcess b hb a κ u t p| ≤ P.atomicCompensatedBound b hb a κ u T p := by
  filter_upwards [ae_all_iff.mpr (fun i => P.pointLocalTime_regular_ae h0 x (a i))] with p hp
  intro t ht
  have hu : ‖u (p t)‖ ≤ ‖u‖ := u.norm_coe_le_norm (p t)
  have hc : ‖(P.geometry.physicalClock b hb t p : ℝ)‖ ≤
      (P.geometry.physicalSpeedUpper b hb : ℝ) * (T : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.geometry.physicalClock b hb t p).coe_nonneg]
    exact (show (P.geometry.physicalClock b hb t p : ℝ) ≤
      (P.geometry.physicalSpeedUpper b hb : ℝ) * (t : ℝ) from
        (P.geometry.physicalClock_bounds b hb t p).2).trans
      (mul_le_mul_of_nonneg_left ht.2 (P.geometry.physicalSpeedUpper b hb).coe_nonneg)
  have hs : ‖∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p‖ ≤
      ∑ i, |κ i * u (a i)| * P.pointLocalTime (a i) T p := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (P.pointLocalTime_nonneg (a i) t p)]
    exact mul_le_mul_of_nonneg_left ((hp i).2.1 ht.2) (abs_nonneg _)
  change |u (p t) + (P.geometry.physicalClock b hb t p : ℝ) -
    ∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p| ≤ _
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖u (p t) + (P.geometry.physicalClock b hb t p : ℝ)‖ +
        ‖∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p‖ := norm_sub_le _ _
    _ ≤ (‖u (p t)‖ + ‖(P.geometry.physicalClock b hb t p : ℝ)‖) +
        ‖∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hu hc) hs

end TimeTraps.Analysis
