module

public import TimeTraps.Analysis.GraphConservativeMomentPairLaw

@[expose] public section

/-! The actual two-index marginal of any projective sampled Markov law.
Repeated sampling labels are retained by the pullback; strict ordering is
required here only to expose the nondegenerate two-time transition. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem observationFamilyPullback_pair_map (τ : ℕ → ℝ≥0)
    (P : ∀ I : Finset ℝ≥0, Measure (I → α)) (i j : ℕ) :
    (observationFamilyPullback τ P {i, j}).map (fun q => (q ⟨i, by simp⟩, q ⟨j, by simp⟩)) =
      (P {τ i, τ j}).map (fun q => (q ⟨τ i, by simp⟩, q ⟨τ j, by simp⟩)) := by
  have hm : Measurable (fun q : ({i, j} : Finset ℕ) → α =>
      (q ⟨i, by simp⟩, q ⟨j, by simp⟩)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  unfold observationFamilyPullback
  rw [Measure.map_map hm (observationPullbackState_measurable τ {i, j})]
  dsimp only [Function.comp_def, observationPullbackState]
  have htransport (I J : Finset ℝ≥0) (hIJ : I = J)
      (hi : τ i ∈ I) (hj : τ j ∈ I) :
      (P I).map (fun q => (q ⟨τ i, hi⟩, q ⟨τ j, hj⟩)) =
        (P J).map (fun q => (q ⟨τ i, hIJ ▸ hi⟩, q ⟨τ j, hIJ ▸ hj⟩)) := by
    subst J
    rfl
  exact htransport _ _ (by simp) _ _

theorem projectiveMarkov_pair_map (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (τ : ℕ → ℝ≥0) (x : α) {μ : Measure (ℕ → α)}
    (hμ : IsProjectiveLimit μ (observationFamilyPullback τ (markovObservationFamily K x)))
    (i j : ℕ) (hij : τ i < τ j) :
    μ.map (fun q => (q i, q j)) = (K (τ i) x) ⊗ₘ K (τ j - τ i) := by
  let I : Finset ℕ := {i, j}
  let ev : (I → α) → α × α := fun q => (q ⟨i, by simp [I]⟩, q ⟨j, by simp [I]⟩)
  have hEv : Measurable ev := (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hR : Measurable (I.restrict : (ℕ → α) → (I → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  calc
    _ = (μ.map I.restrict).map ev := (Measure.map_map hEv hR).symm
    _ = (observationFamilyPullback τ (markovObservationFamily K x) I).map ev :=
      congrArg (fun ν : Measure (I → α) => ν.map ev) (hμ I)
    _ = (markovObservationFamily K x {τ i, τ j}).map
        (fun q => (q ⟨τ i, by simp⟩, q ⟨τ j, by simp⟩)) :=
      observationFamilyPullback_pair_map τ (markovObservationFamily K x) i j
    _ = _ := markovObservationFamily_pair_map K x hij

end TimeTraps.Probability
