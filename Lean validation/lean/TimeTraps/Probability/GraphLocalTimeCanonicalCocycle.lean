module

public import TimeTraps.Probability.GraphLocalTimeCanonicalPointwise

@[expose] public section

/-! Additivity of the canonical local-time limit follows from the exact
shift identity of its approximants. The global convergence event is
stable under every shift, before any measure or Markov law is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

variable {Ω : Type*}

theorem graphLocalTimeCanonical_shift_tendsto
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (S : ℝ≥0 → Ω → Ω)
    (hA : ∀ n ω s, A n (S s ω) = continuousPathShift s (A n ω) - ContinuousMap.const ℝ≥0 (A n ω s))
    {ω : Ω} {l : C(ℝ≥0, ℝ)} (h : Tendsto (fun n => A n ω) atTop (𝓝 l)) (s : ℝ≥0) :
    Tendsto (fun n => A n (S s ω)) atTop
      (𝓝 (continuousPathShift s l - ContinuousMap.const ℝ≥0 (l s))) := by
  have hc : Continuous (fun q : C(ℝ≥0, ℝ) =>
      continuousPathShift s q - ContinuousMap.const ℝ≥0 (q s)) :=
    (continuousPathShift_continuous s).sub
      (ContinuousMap.continuous_const'.comp (continuous_eval_const s))
  simpa only [hA, Function.comp_def] using hc.continuousAt.tendsto.comp h

theorem GraphLocalTimeCanonicalHasLimit.shift
    {A : ℕ → Ω → C(ℝ≥0, ℝ)} (S : ℝ≥0 → Ω → Ω)
    (hA : ∀ n ω s, A n (S s ω) = continuousPathShift s (A n ω) - ContinuousMap.const ℝ≥0 (A n ω s))
    {ω : Ω} (hω : GraphLocalTimeCanonicalHasLimit A ω) (s : ℝ≥0) :
    GraphLocalTimeCanonicalHasLimit A (S s ω) :=
  ⟨_, graphLocalTimeCanonical_shift_tendsto A S hA hω.tendsto s⟩

theorem GraphLocalTimeCanonicalHasLimit.shift_eq
    {A : ℕ → Ω → C(ℝ≥0, ℝ)} (S : ℝ≥0 → Ω → Ω)
    (hA : ∀ n ω s, A n (S s ω) = continuousPathShift s (A n ω) - ContinuousMap.const ℝ≥0 (A n ω s))
    {ω : Ω} (hω : GraphLocalTimeCanonicalHasLimit A ω) (s : ℝ≥0) :
    graphLocalTimeCanonicalPath A (S s ω) =
      continuousPathShift s (graphLocalTimeCanonicalPath A ω) -
        ContinuousMap.const ℝ≥0 (graphLocalTimeCanonicalPath A ω s) :=
  graphLocalTimeCanonicalPath_eq_of_tendsto A
    (graphLocalTimeCanonical_shift_tendsto A S hA hω.tendsto s)

theorem GraphLocalTimeCanonicalHasLimit.cocycle
    {A : ℕ → Ω → C(ℝ≥0, ℝ)} (S : ℝ≥0 → Ω → Ω)
    (hA : ∀ n ω s, A n (S s ω) = continuousPathShift s (A n ω) - ContinuousMap.const ℝ≥0 (A n ω s))
    {ω : Ω} (hω : GraphLocalTimeCanonicalHasLimit A ω) (s t : ℝ≥0) :
    graphLocalTimeCanonicalPath A ω (s + t) = graphLocalTimeCanonicalPath A ω s +
      graphLocalTimeCanonicalPath A (S s ω) t := by
  have he := congrArg (fun q : C(ℝ≥0, ℝ) => q t) (hω.shift_eq S hA s)
  change graphLocalTimeCanonicalPath A (S s ω) t =
    graphLocalTimeCanonicalPath A ω (s + t) - graphLocalTimeCanonicalPath A ω s at he
  linarith

theorem GraphLocalTimeCanonicalHasLimit.pointwise_cocycle
    {A : ℕ → Ω → C(ℝ≥0, ℝ)} (S : ℝ≥0 → Ω → Ω)
    (hA : ∀ n ω s, A n (S s ω) = continuousPathShift s (A n ω) - ContinuousMap.const ℝ≥0 (A n ω s))
    {ω : Ω} (hω : GraphLocalTimeCanonicalHasLimit A ω) (s t : ℝ≥0) :
    graphLocalTimePointwisePath A (s + t) ω = graphLocalTimePointwisePath A s ω +
      graphLocalTimePointwisePath A t (S s ω) := by
  rw [graphLocalTimePointwisePath_eq_canonical A hω,
    graphLocalTimePointwisePath_eq_canonical A hω,
    graphLocalTimePointwisePath_eq_canonical A (hω.shift S hA s)]
  exact hω.cocycle S hA s t

end TimeTraps.Probability
