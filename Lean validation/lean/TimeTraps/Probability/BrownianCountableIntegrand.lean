module

public import TimeTraps.Probability.BrownianCountableIntegrandApproximation
public import TimeTraps.Probability.BrownianAdaptedContinuousIntegrand

@[expose] public section

/-! A bounded Borel scalar function, continuous outside a countable set,
gives an actual closed Brownian integrand on every finite horizon. The
approximants are the original-filtration adapted left dyadic samples;
their canonical integrals are the actual finite Brownian increment sums.
No predictable-density premise or continuity of every composed path is
used. Values at exceptional levels, including the initial value, may be
arbitrary subject to the bound. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {C : Set ℝ} {M : ℝ≥0}

theorem brownianCountable_coefficient_adapted (hBm : ∀ t, Measurable (B t))
    (hg : Measurable g) (t : ℝ≥0) :
    StronglyMeasurable[brownianNaturalFiltration B hBm t] (fun ω => g (B t ω)) :=
  (hg.comp (brownianNaturalFiltration_stronglyAdapted B hBm t).measurable).stronglyMeasurable

def brownianCountableStepIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g)
    (hb : ∀ z, |g z| ≤ M.val) (T : ℝ≥0) (n : ℕ) : brownianIntegralSpace B hBm P :=
  brownianAdaptedContinuousStepIntegrand hB hBm (brownianCountable_coefficient_adapted hBm hg)
    (fun t ω => hb (B t ω)) T n

theorem brownianCountableStepIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g)
    (hb : ∀ z, |g z| ≤ M.val) (T : ℝ≥0) (n : ℕ) :
    (brownianCountableStepIntegrand hB hBm hg hb T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      =ᵐ[volume.prod P] brownianSquareStepProcess (fun t ω => g (B t ω)) T n :=
  brownianAdaptedContinuousStepIntegrand_coe hB hBm (brownianCountable_coefficient_adapted hBm hg)
    (fun t ω => hb (B t ω)) T n

theorem brownianCountableStep_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g)
    (hb : ∀ z, |g z| ≤ M.val) (T : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianCountableStepIntegrand hB hBm hg hb T n) =ᵐ[P]
      brownianStepIntegral B (brownianDyadicGrid T n)
        (fun i ω => g (B (brownianDyadicGrid T n i.castSucc) ω)) :=
  brownianAdaptedContinuousStep_integral_ae hB hBm (brownianCountable_coefficient_adapted hBm hg)
    (fun t ω => hb (B t ω)) T n

theorem brownianCountable_mem_integralSpace (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    brownianAdaptedContinuousProcessL2 hB.toIsPreBrownianReal (hg.comp hjoint)
      (fun t ω => hb (B t ω)) T ∈ brownianIntegralSpace B hBm P := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hconv := brownianBoundedStep_L2_tendsto (hg.comp hjoint) (fun t ω => hb (B t ω)) T
    (brownianCountable_step_tendsto_ae hB hjoint hC hc T)
    (fun n => (brownianCountableStepIntegrand hB.toIsPreBrownianReal hBm hg hb T n :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)))
    (brownianAdaptedContinuousProcessL2 hB.toIsPreBrownianReal (hg.comp hjoint)
      (fun t ω => hb (B t ω)) T)
    (brownianCountableStepIntegrand_coe hB.toIsPreBrownianReal hBm hg hb T)
    (brownianAdaptedContinuousProcessL2_coe hB.toIsPreBrownianReal (hg.comp hjoint)
      (fun t ω => hb (B t ω)) T)
  have hclosed : IsClosed (brownianIntegralSpace B hBm P : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure
  exact hclosed.mem_of_tendsto hconv (Eventually.of_forall (fun n =>
    (brownianCountableStepIntegrand hB.toIsPreBrownianReal hBm hg hb T n).property))

def brownianCountableIntegrand (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  ⟨brownianAdaptedContinuousProcessL2 hB.toIsPreBrownianReal (hg.comp hjoint)
      (fun t ω => hb (B t ω)) T,
    brownianCountable_mem_integralSpace hB hBm hjoint hg hb hC hc T⟩

theorem brownianCountableIntegrand_coe (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] brownianBoundedProcess B g T :=
  brownianAdaptedContinuousProcessL2_coe hB.toIsPreBrownianReal (hg.comp hjoint)
    (fun t ω => hb (B t ω)) T

theorem brownianCountableStepIntegrand_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    Tendsto (fun n => brownianCountableStepIntegrand hB.toIsPreBrownianReal hBm hg hb T n)
      atTop (𝓝 (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T)) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_subtype_rng.mpr
  exact brownianBoundedStep_L2_tendsto (hg.comp hjoint) (fun t ω => hb (B t ω)) T
    (brownianCountable_step_tendsto_ae hB hjoint hC hc T) _ _
    (brownianCountableStepIntegrand_coe hB.toIsPreBrownianReal hBm hg hb T)
    (brownianCountableIntegrand_coe hB hBm hjoint hg hb hC hc T)

def brownianCountableIntegral (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianIntegral hB.toIsPreBrownianReal (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T)

theorem brownianCountableStepIntegral_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB.toIsPreBrownianReal
      (brownianCountableStepIntegrand hB.toIsPreBrownianReal hBm hg hb T n)) atTop
      (𝓝 (brownianCountableIntegral hB hBm hjoint hg hb hC hc T)) :=
  (brownianIntegral hB.toIsPreBrownianReal).continuous.continuousAt.tendsto.comp
    (brownianCountableStepIntegrand_tendsto hB hBm hjoint hg hb hC hc T)

end TimeTraps.Probability

end
