module

public import TimeTraps.Probability.GraphAtomicCompensatedData
public import TimeTraps.Probability.GraphPhysicalClockMeasure
public import TimeTraps.Probability.StieltjesCompensatedPath
public import TimeTraps.Probability.MartingaleStieltjesExpectation

@[expose] public section

/-! Survival-weighted increments of the original graph Dynkin expression
have the actual finite-horizon running-cost residual as their limit.
The contact terms cancel by the verified Stieltjes support identity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal Topology

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.atomicFiniteResidual
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (u : C(GraphRealization P.geometry, ℝ))
    (T : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.atomicSurvival a κ T p * u (p T) - u (p 0) +
    ∫ r in Ioc (0 : ℝ) (T : ℝ), P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal)

theorem GraphShiftedContactOperatorProblem.atomicSurvivalLoss_contact_cancel
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry)
    (u : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) (T : ℝ), u (p r.toNNReal) ∂(P.atomicSurvivalLossStieltjes a κ hκ p).measure) =
      ∑ i, (κ i * u (a i)) * ∫ r in Ioc (0 : ℝ) (T : ℝ),
        1 - P.atomicSurvivalLossStieltjes a κ hκ p (r.toNNReal : ℝ) ∂(P.pointLocalTimeStieltjes (a i) p).measure := by
  apply (P.atomicSurvivalLoss_weighted_contact a κ hκ p u u.continuous T).2.trans
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  change Real.exp (-P.atomicHazardStieltjes a κ hκ p r) =
    1 - (1 - Real.exp (-P.atomicHazardStieltjes a κ hκ p (r.toNNReal : ℝ)))
  rw [Real.coe_toNNReal _ hr.1.le]
  ring

theorem GraphShiftedContactOperatorProblem.atomicCompensatedProcess_weighted_limit
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x,
      Tendsto (fun n => martingaleDyadicWeightedSum (P.atomicCompensatedProcess b hb a κ u)
        (P.atomicSurvival a κ) T n p) atTop (𝓝 (P.atomicFiniteResidual b a κ u T p)) := by
  filter_upwards [P.atomicSurvival_eq_one_sub_loss_ae h0 x a κ hκ,
    ae_all_iff.mpr (fun i => P.pointLocalTime_eq_path_ae h0 x (a i))] with p hH hL
  let K := P.atomicSurvivalLossStieltjes a κ hκ p
  let B := P.geometry.physicalClockStieltjes b hb p
  let L := fun i => P.pointLocalTimeStieltjes (a i) p
  let q := fun t : ℝ≥0 => u (p t)
  have hM (t : ℝ≥0) : P.atomicCompensatedProcess b hb a κ u t p =
      q t + B (t : ℝ) - ∑ i, (κ i * u (a i)) * L i (t : ℝ) := by
    change u (p t) + (P.geometry.physicalClock b hb t p : ℝ) -
      ∑ i, κ i * u (a i) * P.pointLocalTime (a i) t p = _
    rw [← P.geometry.physicalClockStieltjes_apply b hb p t]
    congr 2
    funext i
    change κ i * u (a i) * P.pointLocalTime (a i) t p =
      κ i * u (a i) * P.pointLocalTimePath (a i) p (t : ℝ).toNNReal
    rw [Real.toNNReal_coe, hL i t]
  have he (n : ℕ) : martingaleDyadicWeightedSum (P.atomicCompensatedProcess b hb a κ u)
      (P.atomicSurvival a κ) T n p =
      dyadicWeightedIncrement (fun t => 1 - K (t : ℝ))
        (fun t => q t + B (t : ℝ) - ∑ i, (κ i * u (a i)) * L i (t : ℝ)) T n := by
    simp only [martingaleDyadicWeightedSum, dyadicWeightedIncrement, hH, hM, K]
  have hlim := dyadicWeightedIncrement_contact_cancel_tendsto K B L q (fun i => κ i * u (a i))
    (P.atomicSurvivalLossStieltjes_continuous a κ hκ p) (u.continuous.comp p.continuous) T
    (P.atomicSurvivalLoss_contact_cancel a κ hκ p u T)
  have hR : ((1 - K (T : ℝ)) * q T - (1 - K 0) * q 0) +
      (∫ r in Ioc (0 : ℝ) (T : ℝ), 1 - K (r.toNNReal : ℝ) ∂B.measure) =
      P.atomicFiniteResidual b a κ u T p := by
    have hzero : K 0 = 0 := P.atomicSurvivalLossStieltjes_zero a κ hκ p
    rw [hzero, sub_zero, one_mul]
    change (1 - P.atomicSurvivalLossStieltjes a κ hκ p (T : ℝ)) * q T - q 0 + _ = _
    rw [← hH T]
    have hI : (∫ r in Ioc (0 : ℝ) (T : ℝ), 1 - K (r.toNNReal : ℝ) ∂B.measure) =
        ∫ r in Ioc (0 : ℝ) (T : ℝ), P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal) := by
      simp only [K, ← hH]
      exact P.geometry.physicalClockStieltjes_weighted_integral b hb p (fun t => P.atomicSurvival a κ t p) T
    rw [hI]
    rfl
  rw [hR] at hlim
  exact hlim.congr' (Eventually.of_forall (fun n => (he n).symm))

end TimeTraps.Analysis
