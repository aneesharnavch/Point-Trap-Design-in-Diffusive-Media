module

public import TimeTraps.Probability.BrownianDenseCoupling
public import TimeTraps.Probability.BrownianFiniteMarginals

@[expose] public section

/-! An actual real Brownian process. The underlying probability measure was
constructed by countable projective extension; the paths were obtained by
almost-sure dyadic chaining. Coupling with arbitrary real time coordinates
now identifies every finite-dimensional law, including the empty marginal. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownianDyadicPath_finset_hasLaw (I : Finset ℝ≥0) :
    HasLaw (fun ω : ℕ → ℝ => I.restrict (fun t => brownianDyadicPath t ω))
      (BrownianReal.projectiveFamily I) brownianDyadicMeasure := by
  classical
  let : Encodable I := Encodable.ofCountable I
  let τ : ℕ → ℝ≥0 := fun n => (Encodable.decode n : Option I).elim 0 Subtype.val
  have he (i : I) : τ (Encodable.encode i) = i := by simp [τ]
  have h := (brownianSequence_finset_hasLaw τ I Encodable.encode he).comp
    (brownianDyadicPath_sequence_hasLaw τ)
  change HasLaw (fun ω : ℕ → ℝ => fun i : I => brownianDyadicPath (τ (Encodable.encode i)) ω)
    (BrownianReal.projectiveFamily I) brownianDyadicMeasure at h
  exact h.congr (Filter.Eventually.of_forall (fun ω => funext (fun i =>
    congrArg (fun t => brownianDyadicPath t ω) (he i).symm)))

theorem brownianDyadicPath_isPreBrownianReal :
    IsPreBrownianReal brownianDyadicPath brownianDyadicMeasure where
  hasLaw := brownianDyadicPath_finset_hasLaw

theorem brownianDyadicPath_isBrownianReal :
    IsBrownianReal brownianDyadicPath brownianDyadicMeasure where
  toIsPreBrownianReal := brownianDyadicPath_isPreBrownianReal
  cont := brownianDyadicPath_continuous_ae

theorem real_brownian_process_exists :
    ∃ B : ℝ≥0 → (ℕ → ℝ) → ℝ, IsBrownianReal B brownianDyadicMeasure :=
  ⟨brownianDyadicPath, brownianDyadicPath_isBrownianReal⟩

end TimeTraps.Probability
