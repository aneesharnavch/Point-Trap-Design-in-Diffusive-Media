module

public import TimeTraps.Probability.GraphConservativeOccupationPotentialData

@[expose] public section

/-! The exact kernel pairing is a continuous linear functional on graph
functions. Its commutation with the genuine Bochner integral will provide
the time/state Fubini step in the Kac potential identity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.occupationPairingL
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) :
    C(GraphRealization P.geometry, ℝ) →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp ((P.realizedFeller s).comp
    (ContinuousLinearMap.mul ℝ C(GraphRealization P.geometry, ℝ) f))

theorem GraphShiftedContactOperatorProblem.occupationPairingL_apply
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) :
    P.occupationPairingL s x f g = ∫ y, f y * g y ∂P.realizedTransition s x :=
  P.realizedFeller_apply s (f * g) x

theorem GraphShiftedContactOperatorProblem.occupationPairingL_markovPair
    (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) :
    markovOccupationPair P.realizedTransition x f g s t =
      P.occupationPairingL s x f (P.realizedFeller (t - s) g) := by
  rw [P.occupationPairingL_apply]
  unfold markovOccupationPair
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => congrArg (fun z => f y * z)
    (P.realizedFeller_apply (t - s) g y).symm)

theorem GraphShiftedContactOperatorProblem.realizedFeller_action_continuous
    (P : GraphShiftedContactOperatorProblem V E) :
    Continuous (fun p : ℝ≥0 × C(GraphRealization P.geometry, ℝ) => P.realizedFeller p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using P.realizedFeller_contraction t f g
  · exact P.realizedFeller_strong_continuous

theorem GraphShiftedContactOperatorProblem.occupationPotential_pairing_continuous
    (P : GraphShiftedContactOperatorProblem V E)
    (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    Continuous (fun s : ℝ => P.realizedFeller s.toNNReal (f * P.occupationPotential g (T - s))) :=
  P.realizedFeller_action_continuous.comp (continuous_real_toNNReal.prodMk
    (continuous_const.mul ((P.occupationPotential_continuous g).comp (continuous_const.sub continuous_id))))


theorem GraphShiftedContactOperatorProblem.occupationPotential_kernelPair_continuous
    (P : GraphShiftedContactOperatorProblem V E)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    Continuous (fun s : ℝ => ∫ y, f y * P.occupationPotential g (T - s) y
      ∂P.realizedTransition s.toNNReal x) := by
  have hc := (ContinuousMap.evalCLM ℝ x).continuous.comp (P.occupationPotential_pairing_continuous f g T)
  exact hc.congr (fun s => P.realizedFeller_apply s.toNNReal (f * P.occupationPotential g (T - s)) x)

theorem GraphShiftedContactOperatorProblem.occupationPotential_kernelPair_integrable
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    Integrable (fun y => f y * P.occupationPotential g T y) (P.realizedTransition s x) :=
  P.realizedFeller_integrable s (f * P.occupationPotential g T) x

end TimeTraps.Analysis
