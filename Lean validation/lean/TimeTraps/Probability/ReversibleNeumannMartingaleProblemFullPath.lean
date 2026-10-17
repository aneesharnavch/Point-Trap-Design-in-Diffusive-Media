module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemPathLaw
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section

/-! Uniqueness of the Borel law on continuous paths over the entire
nonnegative time axis, with the topology of uniform convergence on compact
time intervals. Completeness and countable compact exhaustion give the
Polish path space; dense evaluations give a measurable embedding. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval TopologicalSpace
open scoped NNReal ENNReal Topology

abbrev ReversibleNeumannFullPath := C(ℝ≥0, ℝ)

instance reversibleNeumannFullPathMeasurableSpace : MeasurableSpace ReversibleNeumannFullPath := borel _

instance reversibleNeumannFullPathBorelSpace : BorelSpace ReversibleNeumannFullPath := ⟨rfl⟩

def reversibleNeumannFullPathSample (p : ReversibleNeumannFullPath) : ℕ → ℝ :=
  fun n => p (denseSeq ℝ≥0 n)

theorem reversibleNeumannFullPathSample_measurableEmbedding :
    MeasurableEmbedding reversibleNeumannFullPathSample := by
  have hc : Continuous reversibleNeumannFullPathSample :=
    continuous_pi (fun _ => continuous_eval_const _)
  apply hc.measurableEmbedding
  intro p q hpq
  apply ContinuousMap.coe_injective
  exact (denseRange_denseSeq ℝ≥0).equalizer p.continuous q.continuous hpq

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
variable {G : Filtration ℝ≥0 mΩ} {F : Filtration ℝ≥0 mΩ'}
variable {μ : Measure Ω} {ν : Measure Ω'} {x : ℝ}

def ReversibleNeumannMartingaleProblem.fullPath
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (ω : Ω) : ReversibleNeumannFullPath :=
  ⟨fun t => X t ω, h.path_continuous ω⟩

theorem ReversibleNeumannMartingaleProblem.fullPath_measurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x) : Measurable h.fullPath := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n => ((h.adapted _).mono (G.le _)).measurable)

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem ReversibleNeumannMartingaleProblem.full_path_law_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) : μ.map hX.fullPath = ν.map hY.fullPath := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.map_injective
  rw [Measure.map_map reversibleNeumannFullPathSample_measurableEmbedding.measurable hX.fullPath_measurable,
    Measure.map_map reversibleNeumannFullPathSample_measurableEmbedding.measurable hY.fullPath_measurable]
  exact hX.indexed_observation_law_eq hY (denseSeq ℝ≥0)

theorem ReversibleNeumannMartingaleProblem.full_path_law_reference
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (hx : x ∈ Icc A.source.left A.source.right) :
    μ.map h.fullPath = brownianCompletedMeasure.map
      (ReversibleNeumannMartingaleProblem.fullPath (Ω := BrownianCompletedSample)
        (reversibleResistancePath_martingaleProblem A hx)) :=
  h.full_path_law_eq (Ω' := BrownianCompletedSample)
    (Y := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x t ω)
    (reversibleResistancePath_martingaleProblem A hx)

end TimeTraps.Probability

end
