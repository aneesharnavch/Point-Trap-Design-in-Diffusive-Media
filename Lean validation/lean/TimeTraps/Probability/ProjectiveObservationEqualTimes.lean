module

public import TimeTraps.Probability.ProjectiveObservationPullback
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

@[expose] public section

/-! Equal sampling times give equal states almost surely under the
constructed projective law. Countability gives one common event for
all repeated time labels, as required by the dyadic path construction. -/

namespace TimeTraps.Probability

open MeasureTheory Filter

variable {β α : Type*} [DecidableEq β] [MeasurableSpace α] [MeasurableEq α]

theorem observationFamilyPullback_equal_times (τ : ℕ → β)
    (P : ∀ I : Finset β, Measure (I → α)) (I : Finset ℕ)
    (i j : I) (h : τ i.val = τ j.val) :
    ∀ᵐ q ∂observationFamilyPullback τ P I, q i = q j := by
  apply (ae_map_iff (observationPullbackState_measurable τ I).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j))).mpr
  apply Eventually.of_forall
  intro q
  apply congrArg q
  exact Subtype.ext h

theorem projectiveObservation_equal_times (τ : ℕ → β)
    {P : ∀ I : Finset β, Measure (I → α)} {μ : Measure (ℕ → α)}
    (hμ : IsProjectiveLimit μ (observationFamilyPullback τ P))
    (i j : ℕ) (h : τ i = τ j) : ∀ᵐ q ∂μ, q i = q j := by
  let I : Finset ℕ := {i, j}
  let si : I := ⟨i, by simp [I]⟩
  let sj : I := ⟨j, by simp [I]⟩
  have he := observationFamilyPullback_equal_times τ P I si sj h
  rw [← hμ I] at he
  exact ae_of_ae_map
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable he

theorem projectiveObservation_equal_times_all (τ : ℕ → β)
    {P : ∀ I : Finset β, Measure (I → α)} {μ : Measure (ℕ → α)}
    (hμ : IsProjectiveLimit μ (observationFamilyPullback τ P)) :
    ∀ᵐ q ∂μ, ∀ i j, τ i = τ j → q i = q j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases h : τ i = τ j
  · exact (projectiveObservation_equal_times τ hμ i j h).mono (fun _ he _ => he)
  · exact Eventually.of_forall (fun _ he => (h he).elim)

end TimeTraps.Probability
