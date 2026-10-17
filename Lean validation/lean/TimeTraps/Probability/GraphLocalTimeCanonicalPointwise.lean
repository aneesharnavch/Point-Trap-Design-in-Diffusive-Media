module

public import TimeTraps.Probability.GraphLocalTimeCanonicalScalar
public import TimeTraps.Probability.GraphLocalTimeCanonicalProperties
public import Mathlib.Probability.Process.Adapted

@[expose] public section

/-! The same-time scalar limit is raw adapted whenever the approximants
are. On the one global convergence event it agrees at every time with
the canonical continuous path; no future-event measurability is needed
to prove its raw adaptedness. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

variable {Ω : Type*}

def graphLocalTimePointwisePath (A : ℕ → Ω → C(ℝ≥0, ℝ)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  graphLocalTimeScalarLimit (fun n ω => A n ω t) ω

theorem graphLocalTimePointwisePath_measurable_of_eval [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (t : ℝ≥0)
    (hA : ∀ n, Measurable (fun ω => A n ω t)) : Measurable (graphLocalTimePointwisePath A t) :=
  graphLocalTimeScalarLimit_measurable _ hA

theorem graphLocalTimePointwisePath_eq_canonical (A : ℕ → Ω → C(ℝ≥0, ℝ)) {ω : Ω}
    (hω : GraphLocalTimeCanonicalHasLimit A ω) (t : ℝ≥0) :
    graphLocalTimePointwisePath A t ω = graphLocalTimeCanonicalPath A ω t :=
  graphLocalTimeScalarLimit_eq_of_tendsto _ (hω.eval_tendsto t)

theorem graphLocalTimePointwisePath_congr (A B : ℕ → Ω → C(ℝ≥0, ℝ)) {ω ω' : Ω} (t : ℝ≥0)
    (h : ∀ n, A n ω t = B n ω' t) :
    graphLocalTimePointwisePath A t ω = graphLocalTimePointwisePath B t ω' :=
  graphLocalTimeScalarLimit_congr _ _ h

theorem graphLocalTimePointwisePath_jointlyMeasurable [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (hA : ∀ n, Measurable (A n)) :
    Measurable (fun p : ℝ≥0 × Ω => graphLocalTimePointwisePath A p.1 p.2) := by
  change Measurable (graphLocalTimeScalarLimit (fun n (p : ℝ≥0 × Ω) => A n p.2 p.1))
  apply graphLocalTimeScalarLimit_measurable
  intro n
  exact measurable_uncurry_of_continuous_of_measurable (fun ω => (A n ω).continuous)
    (fun t => (continuous_eval_const t).measurable.comp (hA n))

theorem graphLocalTimePointwisePath_stronglyAdapted {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (A : ℕ → Ω → C(ℝ≥0, ℝ))
    (hA : ∀ n, StronglyAdapted ℱ (fun t ω => A n ω t)) :
    StronglyAdapted ℱ (graphLocalTimePointwisePath A) := by
  intro t
  have h : Measurable[ℱ t] (graphLocalTimePointwisePath A t) :=
    @graphLocalTimePointwisePath_measurable_of_eval Ω (ℱ t) A t (fun n => (hA n t).measurable)
  exact h.stronglyMeasurable

theorem graphLocalTimePointwisePath_indistinguishable [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (μ : Measure Ω)
    (hA : ∀ᵐ ω ∂μ, GraphLocalTimeCanonicalHasLimit A ω) :
    ∀ᵐ ω ∂μ, ∀ t, graphLocalTimePointwisePath A t ω = graphLocalTimeCanonicalPath A ω t :=
  hA.mono (fun _ hω t => graphLocalTimePointwisePath_eq_canonical A hω t)

theorem graphLocalTimePointwisePath_continuous_ae [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (μ : Measure Ω)
    (hA : ∀ᵐ ω ∂μ, GraphLocalTimeCanonicalHasLimit A ω) :
    ∀ᵐ ω ∂μ, Continuous (fun t => graphLocalTimePointwisePath A t ω) := by
  filter_upwards [graphLocalTimePointwisePath_indistinguishable A μ hA] with ω hω
  simpa only [hω] using (graphLocalTimeCanonicalPath A ω).continuous

end TimeTraps.Probability

end
