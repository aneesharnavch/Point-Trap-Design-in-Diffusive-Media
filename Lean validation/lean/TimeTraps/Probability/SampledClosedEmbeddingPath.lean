module

public import TimeTraps.Probability.SampledFourthMomentVersion
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! The reconstructed coordinate path remains in a closed embedded state
space. Inverting that embedding gives a state-valued continuous path,
including a fixed state on the exceptional set. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

variable {K E : Type*} [TopologicalSpace K] [NormedAddCommGroup E] [CompleteSpace E]
variable {c : K → E}

theorem FourthDyadicRegular.path_mem_range (hc : IsClosedEmbedding c) {v : ℕ → K}
    (hv : FourthDyadicRegular (c ∘ v)) (t : ℝ≥0) : fourthDyadicPath t (c ∘ v) ∈ range c :=
  hc.isClosed_range.mem_of_tendsto (hv.tendsto t)
    (Eventually.of_forall (fun n => ⟨v (Nat.pair n (brownianDyadicFloor t n)), rfl⟩))

noncomputable def sampledEmbeddedPath (hc : IsClosedEmbedding c)
    (x₀ : K) (v : ℕ → K) (t : ℝ≥0) : K := by
  classical
  exact if hv : FourthDyadicRegular (c ∘ v) then
    hc.isEmbedding.toHomeomorph.symm ⟨fourthDyadicPath t (c ∘ v), hv.path_mem_range hc t⟩
    else x₀

theorem sampledEmbeddedPath_coordinates (hc : IsClosedEmbedding c)
    (x₀ : K) (v : ℕ → K) (t : ℝ≥0) :
    c (sampledEmbeddedPath hc x₀ v t) =
      if FourthDyadicRegular (c ∘ v) then fourthDyadicPath t (c ∘ v) else c x₀ := by
  classical
  by_cases hv : FourthDyadicRegular (c ∘ v)
  · simp only [sampledEmbeddedPath, dif_pos hv, if_pos hv]
    exact congrArg Subtype.val (hc.isEmbedding.toHomeomorph.apply_symm_apply _)
  · simp only [sampledEmbeddedPath, dif_neg hv, if_neg hv]

theorem sampledEmbeddedPath_continuous (hc : IsClosedEmbedding c)
    (x₀ : K) (v : ℕ → K) : Continuous (sampledEmbeddedPath hc x₀ v) := by
  apply hc.isEmbedding.continuous_iff.mpr
  change Continuous (fun t => c (sampledEmbeddedPath hc x₀ v t))
  simp only [sampledEmbeddedPath_coordinates]
  by_cases hv : FourthDyadicRegular (c ∘ v)
  · simpa only [if_pos hv] using hv.continuous
  · simp only [if_neg hv]
    exact continuous_const

theorem sampledEmbeddedPath_recovers (hc : IsClosedEmbedding c)
    (x₀ : K) {v : ℕ → K} (hv : FourthDyadicRegular (c ∘ v)) (i : ℕ) :
    sampledEmbeddedPath hc x₀ v (brownianDyadicTime i) = v i := by
  apply hc.injective
  rw [sampledEmbeddedPath_coordinates hc x₀ v _, if_pos hv, hv.path_eq_coordinate]
  rfl

end TimeTraps.Probability
