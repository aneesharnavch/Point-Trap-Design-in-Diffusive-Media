module

public import TimeTraps.Probability.GaussianExtensionCountable
public import TimeTraps.Probability.BrownianDenseFamily

@[expose] public section

/-! An actual probability-space realization of Brownian finite-dimensional
laws on a countable dense sequence of nonnegative times. Equal times give
equal coordinates simultaneously almost surely. Continuity of paths and
extension to all real times are subsequent construction steps. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal

noncomputable def brownianSequenceMeasure (τ : ℕ → ℝ≥0) : Measure (ℕ → ℝ) :=
  gaussianCountableExtension (brownianSequenceFamily τ)

instance brownianSequenceMeasure_probability (τ : ℕ → ℝ≥0) :
    IsProbabilityMeasure (brownianSequenceMeasure τ) := by
  unfold brownianSequenceMeasure
  infer_instance

theorem brownianSequence_hasLaw (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    HasLaw (fun ω : ℕ → ℝ => I.restrict ω) (brownianSequenceFamily τ I)
      (brownianSequenceMeasure τ) := by
  refine ⟨(measurable_pi_lambda _ fun _ => measurable_pi_apply _).aemeasurable, ?_⟩
  exact gaussianCountableExtension_isProjectiveLimit (brownianSequenceFamily τ)
    (brownianSequenceFamily_projective τ) I

theorem brownianSequence_eval_hasLaw (τ : ℕ → ℝ≥0) (n : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω n) (gaussianReal 0 (τ n)) (brownianSequenceMeasure τ) := by
  have h : HasLaw (fun x : ({n} : Finset ℕ) → ℝ => x ⟨n, by simp⟩)
      (gaussianReal 0 (τ n)) (brownianSequenceFamily τ {n}) :=
    ⟨(measurable_pi_apply _).aemeasurable, brownianSequenceFamily_eval τ {n} ⟨n, by simp⟩⟩
  exact h.comp (brownianSequence_hasLaw τ {n})

theorem brownianSequence_increment_hasLaw (τ : ℕ → ℝ≥0) (n m : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω n - ω m) (gaussianReal 0 (nndist (τ n).val (τ m).val))
      (brownianSequenceMeasure τ) := by
  have h : HasLaw (fun x : ({n, m} : Finset ℕ) → ℝ => x ⟨n, by simp⟩ - x ⟨m, by simp⟩)
      (gaussianReal 0 (nndist (τ n).val (τ m).val)) (brownianSequenceFamily τ {n, m}) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,
      brownianSequenceFamily_increment τ {n, m} ⟨n, by simp⟩ ⟨m, by simp⟩⟩
  exact h.comp (brownianSequence_hasLaw τ {n, m})

theorem brownianSequence_duplicate_ae (τ : ℕ → ℝ≥0) {n m : ℕ} (hτ : τ n = τ m) :
    ∀ᵐ ω ∂brownianSequenceMeasure τ, ω n = ω m := by
  have h := brownianSequence_increment_hasLaw τ n m
  rw [hτ, nndist_self, gaussianReal_zero_var] at h
  exact h.ae_eq_of_dirac.mono (fun _ hω => sub_eq_zero.mp hω)

theorem brownianSequence_consistent_ae (τ : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂brownianSequenceMeasure τ, ∀ n m, τ n = τ m → ω n = ω m := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro m
  by_cases hτ : τ n = τ m
  · exact (brownianSequence_duplicate_ae τ hτ).mono (fun _ hω _ => hω)
  · exact Filter.Eventually.of_forall (fun _ he => (hτ he).elim)

noncomputable def brownianDenseTime : ℕ → ℝ≥0
  | 0 => 0
  | n + 1 => denseSeq ℝ≥0 n

theorem brownianDenseTime_dense : DenseRange brownianDenseTime := by
  apply (denseRange_denseSeq ℝ≥0).mono
  rintro t ⟨n, rfl⟩
  exact ⟨n + 1, rfl⟩

noncomputable def brownianDenseMeasure : Measure (ℕ → ℝ) :=
  brownianSequenceMeasure brownianDenseTime

instance brownianDenseMeasure_probability : IsProbabilityMeasure brownianDenseMeasure :=
  brownianSequenceMeasure_probability brownianDenseTime

theorem brownianDenseMeasure_hasLaw (I : Finset ℕ) :
    HasLaw (fun ω : ℕ → ℝ => I.restrict ω) (brownianSequenceFamily brownianDenseTime I)
      brownianDenseMeasure := brownianSequence_hasLaw brownianDenseTime I

theorem brownianDenseMeasure_start_zero : ∀ᵐ ω ∂brownianDenseMeasure, ω 0 = 0 := by
  have h := brownianSequence_eval_hasLaw brownianDenseTime 0
  rw [brownianDenseTime, gaussianReal_zero_var] at h
  exact h.ae_eq_of_dirac

theorem brownianDenseMeasure_consistent :
    ∀ᵐ ω ∂brownianDenseMeasure, ∀ n m, brownianDenseTime n = brownianDenseTime m → ω n = ω m :=
  brownianSequence_consistent_ae brownianDenseTime

end TimeTraps.Probability
