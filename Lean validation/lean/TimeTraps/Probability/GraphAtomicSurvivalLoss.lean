module

public import TimeTraps.Probability.GraphAtomicHazardContact
public import TimeTraps.Probability.StieltjesExponentialSubstitution

@[expose] public section

/-! The actual continuous increasing loss of survival and its weighted
contact formula. This is the finite-variation cancellation required by
the original Robin equation, with no positivity assumption on its test
function and no restriction to edge-interior contacts. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.atomicSurvivalLossStieltjes
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) : StieltjesFunction ℝ :=
  stieltjesExponential (P.atomicHazardStieltjes a κ hκ p) (P.atomicHazardStieltjes_continuous a κ hκ p)

theorem GraphShiftedContactOperatorProblem.atomicSurvivalLossStieltjes_continuous
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) :
    Continuous (P.atomicSurvivalLossStieltjes a κ hκ p) :=
  stieltjesExponential_continuous _ _

theorem GraphShiftedContactOperatorProblem.atomicSurvivalLossStieltjes_bounds
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) (r : ℝ) :
    0 ≤ P.atomicSurvivalLossStieltjes a κ hκ p r ∧ P.atomicSurvivalLossStieltjes a κ hκ p r ≤ 1 := by
  change 0 ≤ 1 - Real.exp (-P.atomicHazardStieltjes a κ hκ p r) ∧
    1 - Real.exp (-P.atomicHazardStieltjes a κ hκ p r) ≤ 1
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (P.atomicHazardStieltjes_nonneg a κ hκ p r))
  constructor
  · linarith
  · linarith [Real.exp_pos (-P.atomicHazardStieltjes a κ hκ p r)]

theorem GraphShiftedContactOperatorProblem.atomicSurvivalLossStieltjes_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) :
    P.atomicSurvivalLossStieltjes a κ hκ p 0 = 0 := by
  change 1 - Real.exp (-P.atomicHazardStieltjes a κ hκ p 0) = 0
  rw [P.atomicHazardStieltjes_zero, neg_zero, Real.exp_zero, sub_self]

theorem GraphShiftedContactOperatorProblem.atomicSurvival_eq_one_sub_loss_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, ∀ t : ℝ≥0,
      P.atomicSurvival a κ t p = 1 - P.atomicSurvivalLossStieltjes a κ hκ p (t : ℝ) := by
  filter_upwards [P.atomicHazardStieltjes_eq_clock_ae h0 x a κ hκ] with p hp
  intro t
  change Real.exp (-P.atomicKillingClock a κ (t : ℝ) p) =
    1 - (1 - Real.exp (-P.atomicHazardStieltjes a κ hκ p (t : ℝ)))
  rw [hp]
  ring

theorem GraphShiftedContactOperatorProblem.atomicSurvivalLoss_weighted_contact
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry)
    (g : GraphRealization P.geometry → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    IntegrableOn (fun r => g (p r.toNNReal)) (Ioc (0 : ℝ) (T : ℝ))
      (P.atomicSurvivalLossStieltjes a κ hκ p).measure ∧
    (∫ r in Ioc (0 : ℝ) (T : ℝ), g (p r.toNNReal) ∂(P.atomicSurvivalLossStieltjes a κ hκ p).measure) =
      ∑ i, κ i * g (a i) * ∫ r in Ioc (0 : ℝ) (T : ℝ),
        Real.exp (-P.atomicHazardStieltjes a κ hκ p r) ∂P.pointLocalTimeMeasure (a i) p := by
  let K := P.atomicHazardStieltjes a κ hκ p
  have hK : Continuous K := P.atomicHazardStieltjes_continuous a κ hκ p
  have hgp : Continuous (fun t : ℝ≥0 => g (p t)) := hg.comp p.continuous
  have hw : Continuous (fun t : ℝ≥0 => Real.exp (-K (t : ℝ))) :=
    Real.continuous_exp.comp (hK.comp NNReal.continuous_coe).neg
  have hi := stieltjesExponential_weighted_integrable K hK (fun t => g (p t)) hgp T
  have hc := stieltjesExponential_weighted_integral K hK (fun t => g (p t)) hgp T
  have hcontact := P.atomicHazardStieltjes_weighted_contact a κ hκ p
    (fun t => Real.exp (-K (t : ℝ))) hw g T
  refine ⟨hi.1, hc.trans ?_⟩
  have he : (∫ r in Ioc (0 : ℝ) (T : ℝ), g (p r.toNNReal) * Real.exp (-K r) ∂K.measure) =
      ∫ r in Ioc (0 : ℝ) (T : ℝ), Real.exp (-K (r.toNNReal : ℝ)) * g (p r.toNNReal) ∂K.measure := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change g (p r.toNNReal) * Real.exp (-K r) = Real.exp (-K (r.toNNReal : ℝ)) * g (p r.toNNReal)
    rw [Real.coe_toNNReal _ hr.1.le]
    exact mul_comm _ _
  refine he.trans (hcontact.2.trans ?_)
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  change Real.exp (-K (r.toNNReal : ℝ)) = Real.exp (-K r)
  rw [Real.coe_toNNReal _ hr.1.le]

end TimeTraps.Analysis
