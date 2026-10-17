module

public import TimeTraps.Probability.GraphPhysicalKillingLifetime
public import TimeTraps.Probability.GraphAtomicSurvivalPaths

@[expose] public section

/-! The actual original speed stopped before the closed-attainment
lifetime. Its joint almost-everywhere measurability uses the extended
lifetime random variable; no finite lifetime or integrable mean is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.physicalAtomicStoppedSpeed
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (r : ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) : ℝ≥0∞ :=
  {q | ENNReal.ofReal r < P.atomicAttainmentLifetimeValue a κ q}.indicator
    (fun q => ENNReal.ofReal (P.geometry.physicalSpeed b (q.1 r.toNNReal))) p

theorem GraphShiftedContactOperatorProblem.physicalAtomicStoppedSpeed_jointly_aemeasurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (Function.uncurry (P.physicalAtomicStoppedSpeed b a κ))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (exponentialKillingMeasure (P.continuousPathLaw h0 x))) := by
  let inst := P.continuousPathLaw_probability h0 x
  let instE := exponentialKilling_probability (P.continuousPathLaw h0 x)
  have hs : NullMeasurableSet
      {q : ℝ × (GraphContinuousPath P.geometry × ℝ) |
        ENNReal.ofReal q.1 < P.atomicAttainmentLifetimeValue a κ q.2}
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (exponentialKillingMeasure (P.continuousPathLaw h0 x))) :=
    nullMeasurableSet_lt (by fun_prop)
      (P.atomicAttainmentLifetimeValue_aemeasurable h0 x a κ hκ).comp_snd
  have hX : Measurable (fun q : ℝ × (GraphContinuousPath P.geometry × ℝ) =>
      q.2.1 q.1.toNNReal) := by fun_prop
  have hm := ((P.geometry.physicalSpeed_measurable b).comp hX).ennreal_ofReal
  exact hm.aemeasurable.indicator₀ hs

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue_stoppedIntegral
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) :
    P.physicalAtomicAttainmentLifetimeValue b hb a κ p =
      ∫⁻ r in Ioi (0 : ℝ), P.physicalAtomicStoppedSpeed b a κ r p := by
  classical
  rw [P.physicalAtomicAttainmentLifetimeValue_integral]
  let A : Set ℝ := {r | ENNReal.ofReal r < P.atomicAttainmentLifetimeValue a κ p}
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) measurable_const
  change _ = ∫⁻ r in Ioi (0 : ℝ),
    A.indicator (fun r => ENNReal.ofReal (P.geometry.physicalSpeed b (p.1 r.toNNReal))) r
  rw [setLIntegral_indicator hA]
  have he : A ∩ Ioi (0 : ℝ) = positiveTimeBefore (P.atomicAttainmentLifetime a κ p) := by
    ext r
    constructor
    · rintro ⟨hr, hr0⟩
      exact ⟨hr0, (nonnegativeLifetimeValue_lt_iff r hr0.le _).mp hr⟩
    · rintro ⟨hr0, hr⟩
      exact ⟨(nonnegativeLifetimeValue_lt_iff r hr0.le _).mpr hr, hr0⟩
  rw [he]

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue_aemeasurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (P.physicalAtomicAttainmentLifetimeValue b hb a κ)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) := by
  let inst := P.continuousPathLaw_probability h0 x
  let instE := exponentialKilling_probability (P.continuousPathLaw h0 x)
  have hm := (P.physicalAtomicStoppedSpeed_jointly_aemeasurable h0 b x a κ hκ).lintegral_prod_left'
  exact hm.congr (Eventually.of_forall (fun p =>
    (P.physicalAtomicAttainmentLifetimeValue_stoppedIntegral b hb a κ p).symm))

theorem GraphShiftedContactOperatorProblem.physicalAtomicStoppedSpeed_threshold_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (r : ℝ) (hr : 0 ≤ r) :
    P.physicalAtomicStoppedSpeed b a κ r
      =ᵐ[exponentialKillingMeasure (P.continuousPathLaw h0 x)]
      (fun p => if P.atomicKillingClock a κ r p.1 < p.2
        then ENNReal.ofReal (P.geometry.physicalSpeed b (p.1 r.toNNReal)) else 0) := by
  filter_upwards [P.atomicAttainmentLifetime_survival_iff_ae h0 x a κ hκ r hr] with p hp
  have he := (nonnegativeLifetimeValue_lt_iff r hr (P.atomicAttainmentLifetime a κ p)).trans hp
  simp only [physicalAtomicStoppedSpeed, indicator_apply, mem_ofPred_eq]
  exact if_congr he rfl rfl

end TimeTraps.Analysis
