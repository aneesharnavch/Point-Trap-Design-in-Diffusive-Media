module

public import TimeTraps.Probability.MarkovOccupationKac
public import TimeTraps.Probability.GraphConservativeContinuousFiniteLaw

@[expose] public section

/-! Actual signed occupation-product identities for the constructed
continuous graph process. All chronological-law premises are discharged
from the original conservative graph transition kernel. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : GraphContinuousPath P.geometry =>
      (∫ s in 0..T, f (p s.toNNReal)) * (∫ t in 0..T, g (p t.toNNReal)))
        (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  have hm : Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => q.2 q.1) := by fun_prop
  exact markovOccupationKac_integrable (P.continuousPathLaw hκ x) (fun t p => p t) hm f g hT

theorem GraphShiftedContactOperatorProblem.occupation_product_kac
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry,
      (∫ s in 0..T, f (p s.toNNReal)) * (∫ t in 0..T, g (p t.toNNReal))
        ∂P.continuousPathLaw hκ x) =
      (∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair P.realizedTransition x f g s.toNNReal t.toNNReal else 0) +
      (∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair P.realizedTransition x g f s.toNNReal t.toNNReal else 0) := by
  let inst := P.continuousPathLaw_probability hκ x
  let instK : ∀ t, IsMarkovKernel (P.realizedTransition t) :=
    fun t => P.realizedTransition_isMarkov hκ t
  have hm : Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => q.2 q.1) := by fun_prop
  exact markovOccupationKac P.realizedTransition x (P.continuousPathLaw hκ x)
    (fun t p => p t) hm (fun _ _ hst => P.continuousPathLaw_pair hκ x hst) f g hT

theorem GraphShiftedContactOperatorProblem.occupation_square_kac
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry, (∫ s in 0..T, f (p s.toNNReal)) ^ 2
      ∂P.continuousPathLaw hκ x) =
      2 * ∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair P.realizedTransition x f f s.toNNReal t.toNNReal else 0 := by
  simpa only [pow_two, two_mul] using P.occupation_product_kac hκ x f f hT

theorem GraphShiftedContactOperatorProblem.occupation_difference_square_kac
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry,
      ((∫ s in 0..T, f (p s.toNNReal)) - (∫ s in 0..T, g (p s.toNNReal))) ^ 2
        ∂P.continuousPathLaw hκ x) =
      2 * ∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair P.realizedTransition x (f - g) (f - g) s.toNNReal t.toNNReal else 0 := by
  have he (p : GraphContinuousPath P.geometry) :
      (∫ s in 0..T, (f - g) (p s.toNNReal)) =
        (∫ s in 0..T, f (p s.toNNReal)) - ∫ s in 0..T, g (p s.toNNReal) := by
    exact intervalIntegral.integral_sub
      (((f.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable 0 T)
      (((g.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable 0 T)
  simpa only [he] using P.occupation_square_kac hκ x (f - g) hT

end TimeTraps.Analysis
