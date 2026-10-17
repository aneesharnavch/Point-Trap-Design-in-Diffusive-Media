module

public import TimeTraps.Probability.GraphConservativeOccupationConditionalFuture
public import TimeTraps.Probability.GraphConservativeOccupationAdapted
public import TimeTraps.Probability.GraphOccupationL2Data

@[expose] public section

/-! Conditional decomposition of the actual finite-horizon graph
occupation into its adapted prefix and the genuine remaining potential.
The deterministic transition conditional identity is explicit here and
is discharged by the constructed graph Markov law in the final wrapper. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_condExp_of_transition
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (GraphContinuousPath P.geometry)))
    (hX : StronglyAdapted ℱ (fun t (p : GraphContinuousPath P.geometry) => p t))
    {s H : ℝ≥0} (hsH : s ≤ H)
    (hcond : ∀ r : ℝ≥0, s ≤ r →
      (P.continuousPathLaw hκ x)[fun p => f (p r) | ℱ s] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => P.realizedFeller (r - s) f (p s))) :
    (P.continuousPathLaw hκ x)[graphOccupation P.geometry f H | ℱ s] =ᵐ[P.continuousPathLaw hκ x]
      (fun p => graphOccupation P.geometry f s p + P.occupationPotential f (H.val - s.val) (p s)) := by
  let inst := P.continuousPathLaw_probability hκ x
  let A := graphOccupation P.geometry f
  let B : GraphContinuousPath P.geometry → ℝ := fun p => ∫ r in s.val..H.val, f (p r.toNNReal)
  have hsplit : A H = A s + B := by
    funext p
    exact (intervalIntegral.integral_add_adjacent_intervals
      (((f.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable 0 s.val)
      (((f.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable s.val H.val)).symm
  have his : Integrable (A s) (P.continuousPathLaw hκ x) := P.occupation_integrable hκ x f s.coe_nonneg
  have hiH : Integrable (A H) (P.continuousPathLaw hκ x) := P.occupation_integrable hκ x f H.coe_nonneg
  have hiB : Integrable B (P.continuousPathLaw hκ x) := by
    apply (hiH.sub his).congr
    apply Eventually.of_forall
    intro p
    have he := congrFun hsplit p
    change A H p = A s p + B p at he
    change A H p - A s p = B p
    linarith
  have hPast : (P.continuousPathLaw hκ x)[A s | ℱ s] = A s :=
    condExp_of_stronglyMeasurable (ℱ.le s) (P.occupation_prefix_stronglyMeasurable ℱ hX f s) his
  have hFuture := P.occupation_future_condExp_of_transition hκ x f (ℱ s) (ℱ.le s) hsH (hX s) hcond
  have hc := (condExp_congr_ae (Eventually.of_forall (fun p => congrFun hsplit p))).trans
    (condExp_add his hiB (ℱ s))
  have hPastAE : (P.continuousPathLaw hκ x)[A s | ℱ s] =ᵐ[P.continuousPathLaw hκ x] A s :=
    Eventually.of_forall (fun p => congrFun hPast p)
  exact hc.trans (hPastAE.add hFuture)

end TimeTraps.Analysis
