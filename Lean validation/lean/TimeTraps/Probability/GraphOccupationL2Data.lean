module

public import TimeTraps.Probability.OccupationPotentialCauchyData
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! Genuine occupation random variables in the original continuous graph
path law, and their actual L2 classes. Product integrability comes from
the proved signed occupation formula. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false

noncomputable def graphOccupation (G : MetricGraph V E) (f : C(GraphRealization G, ℝ))
    (T : ℝ≥0) (p : GraphContinuousPath G) : ℝ :=
  ∫ s in (0 : ℝ)..(T : ℝ), f (p s.toNNReal)

omit [Nonempty E] in
theorem graphOccupation_stronglyMeasurable (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) : StronglyMeasurable (graphOccupation G f T) := by
  have hm : Measurable (fun q : GraphContinuousPath G × ℝ => f (q.1 q.2.toNNReal)) := by fun_prop
  unfold graphOccupation
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hm.stronglyMeasurable.integral_prod_right

theorem GraphShiftedContactOperatorProblem.occupation_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    MemLp (graphOccupation P.geometry f T) 2 (P.continuousPathLaw hκ x) := by
  apply (memLp_two_iff_integrable_sq (graphOccupation_stronglyMeasurable _ f T).aestronglyMeasurable).mpr
  simpa only [graphOccupation, pow_two] using P.occupation_product_integrable hκ x f f T.coe_nonneg

noncomputable def GraphShiftedContactOperatorProblem.occupationL2
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    Lp ℝ 2 (P.continuousPathLaw hκ x) :=
  (P.occupation_memLp hκ x f T).toLp (graphOccupation P.geometry f T)

theorem GraphShiftedContactOperatorProblem.occupationL2_coe
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    P.occupationL2 hκ x f T =ᵐ[P.continuousPathLaw hκ x] graphOccupation P.geometry f T :=
  (P.occupation_memLp hκ x f T).coeFn_toLp

theorem GraphShiftedContactOperatorProblem.occupationL2_sub_norm_sq
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ‖P.occupationL2 hκ x f T - P.occupationL2 hκ x g T‖ ^ 2 =
      ∫ p, (graphOccupation P.geometry f T p - graphOccupation P.geometry g T p) ^ 2
        ∂P.continuousPathLaw hκ x := by
  let F := P.occupationL2 hκ x f T
  let G := P.occupationL2 hκ x g T
  calc
    _ = ∫ p, (F - G) p ^ 2 ∂P.continuousPathLaw hκ x := by
      simpa only [Lp.toLp_coeFn] using memLp_norm_toLp_sq (Lp.memLp (F - G))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub F G, P.occupationL2_coe hκ x f T,
        P.occupationL2_coe hκ x g T] with p hp hf hg
      rw [hp]
      dsimp only [Pi.sub_apply, F, G]
      rw [hf, hg]

end TimeTraps.Analysis
