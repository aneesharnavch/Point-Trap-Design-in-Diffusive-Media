module

public import TimeTraps.Probability.GraphConservativeOccupationKac
public import TimeTraps.Probability.MarkovOccupationKacTriangle

@[expose] public section

/-! The conventional chronological Kac formula for the actual graph
process, including the signed difference-square needed for local-time
approximation. The horizon may be zero. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_product_kac_triangle
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry,
      (∫ s in 0..T, f (p s.toNNReal)) * (∫ t in 0..T, g (p t.toNNReal))
        ∂P.continuousPathLaw hκ x) =
      (∫ s in 0..T, ∫ t in s..T,
        markovOccupationPair P.realizedTransition x f g s.toNNReal t.toNNReal) +
      (∫ s in 0..T, ∫ t in s..T,
        markovOccupationPair P.realizedTransition x g f s.toNNReal t.toNNReal) := by
  let inst := P.continuousPathLaw_probability hκ x
  let instK : ∀ t, IsMarkovKernel (P.realizedTransition t) :=
    fun t => P.realizedTransition_isMarkov hκ t
  have hm : Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => q.2 q.1) := by fun_prop
  exact markovOccupationKac_upperTriangle P.realizedTransition x (P.continuousPathLaw hκ x)
    (fun t p => p t) hm (fun _ _ hst => P.continuousPathLaw_pair hκ x hst) f g hT

theorem GraphShiftedContactOperatorProblem.occupation_difference_square_kac_triangle
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry,
      ((∫ s in 0..T, f (p s.toNNReal)) - (∫ s in 0..T, g (p s.toNNReal))) ^ 2
        ∂P.continuousPathLaw hκ x) =
      2 * ∫ s in 0..T, ∫ t in s..T,
        markovOccupationPair P.realizedTransition x (f - g) (f - g) s.toNNReal t.toNNReal := by
  have he (p : GraphContinuousPath P.geometry) :
      (∫ s in 0..T, (f - g) (p s.toNNReal)) =
        (∫ s in 0..T, f (p s.toNNReal)) - ∫ s in 0..T, g (p s.toNNReal) := by
    exact intervalIntegral.integral_sub
      (((f.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable 0 T)
      (((g.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable 0 T)
  simpa only [he, pow_two, two_mul] using P.occupation_product_kac_triangle hκ x (f - g) (f - g) hT

end TimeTraps.Analysis
