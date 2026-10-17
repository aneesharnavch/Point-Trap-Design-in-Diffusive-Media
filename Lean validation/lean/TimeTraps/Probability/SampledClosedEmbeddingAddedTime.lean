module

public import TimeTraps.Probability.SampledClosedEmbeddingMeasure
public import TimeTraps.Probability.SampledFourthMomentConvergence

@[expose] public section

/-! The continuous reconstruction also recovers an extra observation at
an arbitrary real time, provided its fourth increments against the dense
observations obey the actual time-distance estimate. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

variable {Ω K E : Type*} [MeasurableSpace Ω] [TopologicalSpace K]
  [NormedAddCommGroup E] [CompleteSpace E]
variable {c : K → E} {X : ℕ → Ω → K} {P : Measure Ω} [IsFiniteMeasure P]

theorem sampledEmbeddedPath_added_time_ae (hc : IsClosedEmbedding c) (x₀ : K)
    (hr : ∀ᵐ ω ∂P, FourthDyadicRegular (fun i => c (X i ω)))
    (t : ℝ≥0) (Z : Ω → K) {C : ℝ}
    (hi : ∀ i, Integrable (fun ω => dist (c (X i ω)) (c (Z ω)) ^ 4) P)
    (hb : ∀ i, (∫ ω, dist (c (X i ω)) (c (Z ω)) ^ 4 ∂P) ≤
      C * dist (brownianDyadicTime i) t ^ 2) :
    (fun ω => sampledEmbeddedPath hc x₀ (fun i => X i ω) t) =ᵐ[P] Z := by
  have ht : Tendsto (fun n => brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n))) atTop (𝓝 t) :=
    NNReal.tendsto_coe.mp (brownianDyadicTime_floor_tendsto t)
  have hm := sampledFourthMoment_tendstoInMeasure
    (fun n => hi (Nat.pair n (brownianDyadicFloor t n)))
    (fun n => hb (Nat.pair n (brownianDyadicFloor t n))) ht
  obtain ⟨u, hu, hlim⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hr, hlim] with ω hω hlimω
  apply hc.injective
  rw [sampledEmbeddedPath_coordinates hc x₀ _ t]
  simp only [Function.comp_def, if_pos hω]
  exact tendsto_nhds_unique ((hω.tendsto t).comp hu.tendsto_atTop) hlimω

theorem sampledEmbeddedPath_added_times_ae (hc : IsClosedEmbedding c) (x₀ : K)
    (hr : ∀ᵐ ω ∂P, FourthDyadicRegular (fun i => c (X i ω)))
    (τ : ℕ → ℝ≥0) (Z : ℕ → Ω → K) {C : ℝ}
    (hi : ∀ i j, Integrable (fun ω => dist (c (X i ω)) (c (Z j ω)) ^ 4) P)
    (hb : ∀ i j, (∫ ω, dist (c (X i ω)) (c (Z j ω)) ^ 4 ∂P) ≤
      C * dist (brownianDyadicTime i) (τ j) ^ 2) :
    ∀ᵐ ω ∂P, ∀ j, sampledEmbeddedPath hc x₀ (fun i => X i ω) (τ j) = Z j ω := by
  apply ae_all_iff.mpr
  intro j
  exact sampledEmbeddedPath_added_time_ae hc x₀ hr (τ j) (Z j) (fun i => hi i j) (fun i => hb i j)

end TimeTraps.Probability
