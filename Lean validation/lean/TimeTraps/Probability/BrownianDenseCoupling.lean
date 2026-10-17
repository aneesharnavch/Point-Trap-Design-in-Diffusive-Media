module

public import TimeTraps.Probability.BrownianSequenceReindex
public import TimeTraps.Probability.BrownianSequenceContinuity

@[expose] public section

/-! Couple the dense grid with any prescribed sequence of real times using
the previously constructed countable Gaussian extension. Uniqueness of
limits in measure identifies every added coordinate with the continuous
grid extension. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def brownianCoupledTime (τ : ℕ → ℝ≥0) (i : ℕ) : ℝ≥0 :=
  if (Nat.unpair i).1 = 0 then brownianDyadicTime (Nat.unpair i).2 else τ (Nat.unpair i).2

theorem brownianCoupledTime_left (τ : ℕ → ℝ≥0) (n : ℕ) :
    brownianCoupledTime τ (Nat.pair 0 n) = brownianDyadicTime n := by
  simp [brownianCoupledTime]

theorem brownianCoupledTime_right (τ : ℕ → ℝ≥0) (n : ℕ) :
    brownianCoupledTime τ (Nat.pair 1 n) = τ n := by
  simp [brownianCoupledTime]

def brownianCoupledLeft (ω : ℕ → ℝ) (n : ℕ) : ℝ := ω (Nat.pair 0 n)

def brownianCoupledRight (ω : ℕ → ℝ) (n : ℕ) : ℝ := ω (Nat.pair 1 n)

theorem brownianCoupledLeft_hasLaw (τ : ℕ → ℝ≥0) :
    HasLaw brownianCoupledLeft brownianDyadicMeasure
      (brownianSequenceMeasure (brownianCoupledTime τ)) := by
  have h := brownianSequence_reindex_hasLaw (brownianCoupledTime τ) (Nat.pair 0)
  have he : brownianCoupledTime τ ∘ Nat.pair 0 = brownianDyadicTime :=
    funext (brownianCoupledTime_left τ)
  rw [he] at h
  exact h

theorem brownianCoupledRight_hasLaw (τ : ℕ → ℝ≥0) :
    HasLaw brownianCoupledRight (brownianSequenceMeasure τ)
      (brownianSequenceMeasure (brownianCoupledTime τ)) := by
  have h := brownianSequence_reindex_hasLaw (brownianCoupledTime τ) (Nat.pair 1)
  have he : brownianCoupledTime τ ∘ Nat.pair 1 = τ := funext (brownianCoupledTime_right τ)
  rw [he] at h
  exact h

theorem brownianCoupledLeft_regular_ae (τ : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂brownianSequenceMeasure (brownianCoupledTime τ),
      BrownianDyadicRegular (brownianCoupledLeft ω) := by
  apply ae_of_ae_map (brownianCoupledLeft_hasLaw τ).aemeasurable
  rw [(brownianCoupledLeft_hasLaw τ).map_eq]
  exact brownianDyadic_regular_ae

theorem brownianCoupledPath_eq_right (τ : ℕ → ℝ≥0) (j : ℕ) :
    (fun ω => brownianDyadicPath (τ j) (brownianCoupledLeft ω)) =ᵐ[
      brownianSequenceMeasure (brownianCoupledTime τ)] (fun ω => brownianCoupledRight ω j) := by
  have hc : TendstoInMeasure (brownianSequenceMeasure (brownianCoupledTime τ))
      (fun n ω => brownianDyadicStep (τ j) n (brownianCoupledLeft ω)) atTop
      (fun ω => brownianCoupledRight ω j) := by
    apply brownianSequence_tendstoInMeasure (brownianCoupledTime τ)
      (fun n => Nat.pair 0 (Nat.pair n (brownianDyadicFloor (τ j) n))) (Nat.pair 1 j)
    simpa only [brownianCoupledTime_left, brownianCoupledTime_right] using
      brownianDyadicTime_floor_tendsto (τ j)
  have hp : TendstoInMeasure (brownianSequenceMeasure (brownianCoupledTime τ))
      (fun n ω => brownianDyadicStep (τ j) n (brownianCoupledLeft ω)) atTop
      (fun ω => brownianDyadicPath (τ j) (brownianCoupledLeft ω)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (measurable_pi_apply _).aestronglyMeasurable
    · exact (brownianCoupledLeft_regular_ae τ).mono (fun _ hω => hω.tendsto (τ j))
  exact tendstoInMeasure_ae_unique hp hc

theorem brownianDyadicPath_sequence_hasLaw (τ : ℕ → ℝ≥0) :
    HasLaw (fun η : ℕ → ℝ => fun j => brownianDyadicPath (τ j) η)
      (brownianSequenceMeasure τ) brownianDyadicMeasure := by
  have hm : Measurable (fun η : ℕ → ℝ => fun j => brownianDyadicPath (τ j) η) :=
    measurable_pi_lambda _ (fun j => brownianDyadicPath_measurable (τ j))
  refine ⟨hm.aemeasurable, ?_⟩
  rw [← (brownianCoupledLeft_hasLaw τ).map_eq,
    Measure.map_map hm (measurable_pi_lambda _ (fun _ => measurable_pi_apply _) :
      Measurable brownianCoupledLeft)]
  have he : (fun ω : ℕ → ℝ => fun j => brownianDyadicPath (τ j) (brownianCoupledLeft ω)) =ᵐ[
      brownianSequenceMeasure (brownianCoupledTime τ)] brownianCoupledRight := by
    filter_upwards [ae_all_iff.mpr (brownianCoupledPath_eq_right τ)] with ω hω
    exact funext hω
  exact (Measure.map_congr he).trans (brownianCoupledRight_hasLaw τ).map_eq

end TimeTraps.Probability
