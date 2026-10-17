module

public import TimeTraps.Analysis.GraphShiftedContactRealizedConservative
public import TimeTraps.Probability.MarkovFiniteKernelPruning

@[expose] public section

/-! Actual finite observation laws of the conservative graph transition.
They are built from the original unshifted heat kernel. Their probability
mass, iterated integrals and consistency under observation deletion are
proved for every graph with zero reactions and positive conductance. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.finiteObservationLaw
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (d : List ℝ≥0) : Measure (Fin d.length → GraphRealization P.geometry) :=
  finiteMarkovKernel P.realizedTransition d x

theorem GraphShiftedContactOperatorProblem.finiteObservationLaw_probability
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (d : List ℝ≥0) :
    IsProbabilityMeasure (P.finiteObservationLaw x d) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  unfold finiteObservationLaw
  infer_instance

theorem GraphShiftedContactOperatorProblem.finiteObservationLaw_first
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (d : List ℝ≥0) :
    (P.finiteObservationLaw x (t :: d)).map (fun q => q 0) = P.realizedTransition t x := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  rw [finiteObservationLaw, ← Kernel.map_apply _ (measurable_pi_apply 0)]
  exact congrArg (fun k => k x) (finiteMarkovKernel_head P.realizedTransition t d)

theorem GraphShiftedContactOperatorProblem.finiteObservationLaw_pruning
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) {d e : List ℝ≥0} (p : ElapsedObservationPruning d e) :
    (P.finiteObservationLaw x d).map p.stateMap = P.finiteObservationLaw x e := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  rw [finiteObservationLaw, ← Kernel.map_apply _ p.stateMap_measurable]
  exact congrArg (fun k => k x) (p.kernel_consistency P.realizedTransition P.realizedTransition_add)

theorem GraphShiftedContactOperatorProblem.finiteObservationLaw_lintegral_cons
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (d : List ℝ≥0)
    {F : (Fin (d.length + 1) → GraphRealization P.geometry) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂P.finiteObservationLaw x (t :: d)) =
      ∫⁻ y, ∫⁻ q, F (Fin.cons y q) ∂P.finiteObservationLaw y d ∂P.realizedTransition t x := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  exact finiteMarkovKernel_lintegral_cons P.realizedTransition t d x hF

end TimeTraps.Analysis
