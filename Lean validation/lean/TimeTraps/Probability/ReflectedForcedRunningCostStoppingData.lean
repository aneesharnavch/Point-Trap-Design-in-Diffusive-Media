module

public import TimeTraps.Probability.ReflectedForcedRunningCost
public import TimeTraps.Probability.ReflectedAtomicLifetimeConvention

@[expose] public section

/-! Literal observations before the paper's first-attainment lifetime.
The extended lifetime retains infinity. Joint almost-everywhere
measurability comes from its actual extended random variable, rather
than an uncountable intersection of fixed-time survival events. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g : ℝ → ℝ}

def reflectedForcedRunningCostObservation (P : SpectralProblem n) (g : ℝ → ℝ)
    (x r : ℝ) (ω : ℕ → ℝ) : ℝ :=
  g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal ω)

def reflectedForcedRunningCostStoppedValue (P : SpectralProblem n) (g : ℝ → ℝ)
    (x r : ℝ) (p : (ℕ → ℝ) × ℝ) : ℝ :=
  {q | ENNReal.ofReal r < reflectedAtomicAttainmentLifetimeValue
    P.length P.diffusivity x P.site P.strength q}.indicator
      (fun q => reflectedForcedRunningCostObservation P g x r q.1) p

theorem reflectedForcedRunningCostObservation_measurable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) :
    Measurable (Function.uncurry (reflectedForcedRunningCostObservation P g x)) := by
  have he : Function.uncurry (reflectedForcedRunningCostObservation P g x) =
      fun p : ℝ × (ℕ → ℝ) =>
        reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg)
          (foldedTrajectory P.length P.diffusivity x brownianDyadicPath p.1.toNNReal p.2) := by
    funext p
    exact (forcedKinkSource_extension hg
      (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath p.1.toNNReal p.2)).symm
  rw [he]
  have harg : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hm := (foldedTrajectory_joint_measurable P.length P.diffusivity x brownianDyadicPath
    brownianDyadicPath_jointly_measurable).comp harg
  convert! (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg)).continuous.measurable.comp hm using 1

theorem reflectedForcedRunningCostObservation_bound
    (hg : ContinuousOn g (Icc 0 P.length)) (x r : ℝ) (ω : ℕ → ℝ) :
    ‖reflectedForcedRunningCostObservation P g x r ω‖ ≤ ‖forcedKinkSource P g hg‖ :=
  (forcedKinkSource P g hg).norm_coe_le_norm
    ⟨_, foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath r.toNNReal ω⟩

theorem reflectedForcedRunningCostStoppedValue_eq (P : SpectralProblem n)
    (g : ℝ → ℝ) (x r : ℝ) (hr : 0 ≤ r) (p : (ℕ → ℝ) × ℝ) :
    reflectedForcedRunningCostStoppedValue P g x r p =
      if (r : WithTop ℝ) < reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p
      then g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal p.1) else 0 := by
  simp only [reflectedForcedRunningCostStoppedValue, indicator_apply, mem_ofPred_eq,
    reflectedAtomicAttainmentLifetimeValue, contactAttainmentLifetimeValue,
    nonnegativeLifetimeValue_lt_iff r hr, reflectedAtomicAttainmentLifetime,
    reflectedForcedRunningCostObservation]
  rfl

theorem reflectedForcedRunningCostStoppedValue_jointly_aestronglyMeasurable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) :
    AEStronglyMeasurable (Function.uncurry (reflectedForcedRunningCostStoppedValue P g x))
      ((volume.restrict (Ioi (0 : ℝ))).prod (exponentialKillingMeasure brownianDyadicMeasure)) := by
  have hs : NullMeasurableSet
      {p : ℝ × ((ℕ → ℝ) × ℝ) | ENNReal.ofReal p.1 <
        reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p.2}
      ((volume.restrict (Ioi (0 : ℝ))).prod (exponentialKillingMeasure brownianDyadicMeasure)) :=
    nullMeasurableSet_lt (by fun_prop)
      (reflectedAtomicAttainmentLifetimeValue_aemeasurable P.length P.length_pos P.diffusivity
        P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le)).comp_snd
  exact (((reflectedForcedRunningCostObservation_measurable hg x).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).aestronglyMeasurable).indicator₀ hs

theorem reflectedForcedRunningCostStoppedValue_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) (x r : ℝ) :
    Integrable (reflectedForcedRunningCostStoppedValue P g x r)
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  let _ := unitExponential_probability
  have hs : NullMeasurableSet {p : (ℕ → ℝ) × ℝ | ENNReal.ofReal r <
      reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p}
      (exponentialKillingMeasure brownianDyadicMeasure) :=
    nullMeasurableSet_lt aemeasurable_const
      (reflectedAtomicAttainmentLifetimeValue_aemeasurable P.length P.length_pos P.diffusivity
        P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le))
  have hm0 : Measurable (reflectedForcedRunningCostObservation P g x r) :=
    by
      have ha : Measurable (fun ω : ℕ → ℝ => (r, ω)) := measurable_const.prodMk measurable_id
      convert! (reflectedForcedRunningCostObservation_measurable hg x).comp ha using 1
  have ho : Integrable (reflectedForcedRunningCostObservation P g x r) brownianDyadicMeasure := by
    apply (integrable_const ‖forcedKinkSource P g hg‖).mono' hm0.aestronglyMeasurable
    convert! Eventually.of_forall (reflectedForcedRunningCostObservation_bound hg x r) using 1
  convert! (ho.comp_fst (expMeasure 1)).indicator₀ hs using 1

end TimeTraps.Probability

end
