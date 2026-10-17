module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemHistoryData
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Genuine finite-horizon continuous paths of each competitor, with
Borel measurability derived from an injective countable dense evaluation
map on the Polish uniform continuous-path space. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval TopologicalSpace
open scoped NNReal ENNReal Topology

abbrev ReversibleNeumannContinuousPath (H : ℝ≥0) := C(Icc (0 : ℝ≥0) H, ℝ)

instance reversibleNeumannContinuousPathMeasurableSpace (H : ℝ≥0) :
    MeasurableSpace (ReversibleNeumannContinuousPath H) := borel _

instance reversibleNeumannContinuousPathBorelSpace (H : ℝ≥0) :
    BorelSpace (ReversibleNeumannContinuousPath H) := ⟨rfl⟩

def reversibleNeumannContinuousPathSample (H : ℝ≥0) (p : ReversibleNeumannContinuousPath H) : ℕ → ℝ := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, le_rfl, bot_le⟩⟩
  exact fun n => p (denseSeq (Icc (0 : ℝ≥0) H) n)

theorem reversibleNeumannContinuousPathSample_measurableEmbedding (H : ℝ≥0) :
    MeasurableEmbedding (reversibleNeumannContinuousPathSample H) := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, le_rfl, bot_le⟩⟩
  have hc : Continuous (reversibleNeumannContinuousPathSample H) :=
    continuous_pi (fun _ => continuous_eval_const _)
  apply hc.measurableEmbedding
  intro p q hpq
  apply ContinuousMap.coe_injective
  exact (denseRange_denseSeq (Icc (0 : ℝ≥0) H)).equalizer p.continuous q.continuous hpq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {x : ℝ}

def ReversibleNeumannMartingaleProblem.continuousPath
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ℝ≥0) (ω : Ω) :
    ReversibleNeumannContinuousPath H :=
  ⟨fun t => X t.val ω, (h.path_continuous ω).comp continuous_subtype_val⟩

theorem ReversibleNeumannMartingaleProblem.continuousPath_measurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ℝ≥0) :
    Measurable (h.continuousPath H) := by
  apply (reversibleNeumannContinuousPathSample_measurableEmbedding H).measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n => ((h.adapted _).mono (G.le _)).measurable)

end TimeTraps.Probability

end
