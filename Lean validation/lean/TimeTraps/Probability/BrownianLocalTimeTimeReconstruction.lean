module

public import TimeTraps.Probability.BrownianLocalTimeJointVersion
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-! Reconstruct a jointly measurable local-time field from its dyadic time
samples. At each fixed level one measurable event of full measure gives
agreement with the previously constructed global path at every time.
The event is not intersected over the uncountable set of levels. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

def brownianLocalTimeSampleTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n))

theorem brownianLocalTimeSampleTime_measurable (n : ℕ) :
    Measurable (brownianLocalTimeSampleTime n) :=
  (measurable_of_countable (fun k => brownianDyadicTime (Nat.pair n k))).comp
    (brownianDyadicFloor_measurable n)

theorem brownianLocalTimeSampleTime_tendsto (t : ℝ≥0) :
    Tendsto (fun n => brownianLocalTimeSampleTime n t) atTop (𝓝 t) :=
  tendsto_subtype_rng.mpr (brownianDyadicTime_floor_tendsto t)

def brownianLocalTimeSampleAgreement (a : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω =
    brownianLocalTimeGlobalPath a (brownianDyadicTime i) ω

theorem brownianLocalTimeSampleAgreement_measurableSet (a : ℝ) :
    MeasurableSet {ω | brownianLocalTimeSampleAgreement a ω} := by
  change MeasurableSet {ω | ∀ i : ℕ,
    brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω =
      brownianLocalTimeGlobalPath a (brownianDyadicTime i) ω}
  rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_eq_fun _ (brownianLocalTimeGlobalPath_measurable a _)
  let φ : (ℕ → ℝ) → (ℝ × ℝ≥0) × (ℕ → ℝ) :=
    fun ω => ((a, brownianDyadicTime i), ω)
  have hφ : Measurable φ := measurable_const.prodMk measurable_id
  have hm := (brownianLocalTimeJointVersion_jointlyMeasurable
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable).comp hφ
  change Measurable (fun ω : ℕ → ℝ => brownianLocalTimeJointVersion
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a (brownianDyadicTime i) ω) at hm
  exact hm

theorem brownianLocalTimeSampleAgreement_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeSampleAgreement a ω :=
  ae_all_iff.mpr (fun i => brownianDyadicLocalTimeJointVersion_globalPath_ae a (brownianDyadicTime i))

def brownianLocalTimeTimeField (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  (limsup (fun n => ENNReal.ofReal
    (brownianDyadicLocalTimeJointVersion a (brownianLocalTimeSampleTime n t) ω)) atTop).toReal

theorem brownianLocalTimeTimeField_jointlyMeasurable :
    Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) =>
      brownianLocalTimeTimeField p.1.1 p.1.2 p.2) := by
  have hs (n : ℕ) : Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) =>
      brownianDyadicLocalTimeJointVersion p.1.1 (brownianLocalTimeSampleTime n p.1.2) p.2) := by
    let φ : ((ℝ × ℝ≥0) × (ℕ → ℝ)) → (ℝ × ℝ≥0) × (ℕ → ℝ) :=
      fun p => ((p.1.1, brownianLocalTimeSampleTime n p.1.2), p.2)
    have hφ : Measurable φ :=
      (measurable_fst.fst.prodMk ((brownianLocalTimeSampleTime_measurable n).comp
        measurable_fst.snd)).prodMk measurable_snd
    have hm := (brownianLocalTimeJointVersion_jointlyMeasurable
      brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable).comp hφ
    change Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) => brownianLocalTimeJointVersion
      brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable p.1.1 (brownianLocalTimeSampleTime n p.1.2) p.2) at hm
    exact hm
  have hm := (Measurable.limsup (fun n => (hs n).ennreal_ofReal)).ennreal_toReal
  change Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) =>
    brownianLocalTimeTimeField p.1.1 p.1.2 p.2) at hm
  exact hm

theorem brownianLocalTimeTimeField_nonneg (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ brownianLocalTimeTimeField a t ω := ENNReal.toReal_nonneg

theorem brownianLocalTimeTimeField_eq_of_sampleAgreement {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeSampleAgreement a ω) (t : ℝ≥0) :
    brownianLocalTimeTimeField a t ω = brownianLocalTimeGlobalPath a t ω := by
  have he (n : ℕ) : brownianDyadicLocalTimeJointVersion a (brownianLocalTimeSampleTime n t) ω =
      brownianLocalTimeGlobalPath a (brownianLocalTimeSampleTime n t) ω :=
    hω (Nat.pair n (brownianDyadicFloor t n))
  have ht : Tendsto (fun n => brownianDyadicLocalTimeJointVersion a
      (brownianLocalTimeSampleTime n t) ω) atTop (𝓝 (brownianLocalTimeGlobalPath a t ω)) := by
    simp only [he]
    exact (brownianLocalTimeGlobalPath_continuous a ω).continuousAt.tendsto.comp
      (brownianLocalTimeSampleTime_tendsto t)
  have hlim := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht).limsup_eq
  simp only [Function.comp_def] at hlim
  change ENNReal.toReal _ = _
  rw [hlim, ENNReal.toReal_ofReal (brownianLocalTimeGlobalPath_nonneg a t ω)]

theorem brownianLocalTimeTimeField_globalPath_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      brownianLocalTimeTimeField a t ω = brownianLocalTimeGlobalPath a t ω :=
  (brownianLocalTimeSampleAgreement_ae a).mono
    (fun _ hω t => brownianLocalTimeTimeField_eq_of_sampleAgreement hω t)

end TimeTraps.Probability

end
