module

public import TimeTraps.Probability.GraphConservativeOccupationPotentialTranslation

@[expose] public section

/-! Kac's product identity for the actual graph process expressed through
its finite-time Feller potentials. The signed difference-square form is
the exact starting point for quantitative local-time approximation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_product_potential
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry,
      (∫ s in 0..T, f (p s.toNNReal)) * (∫ t in 0..T, g (p t.toNNReal))
        ∂P.continuousPathLaw hκ x) =
      (∫ s in 0..T, ∫ y, f y * P.occupationPotential g (T - s) y ∂P.realizedTransition s.toNNReal x) +
      (∫ s in 0..T, ∫ y, g y * P.occupationPotential f (T - s) y ∂P.realizedTransition s.toNNReal x) := by
  have he (u v : C(GraphRealization P.geometry, ℝ)) :
      (∫ s in 0..T, ∫ t in s..T,
        markovOccupationPair P.realizedTransition x u v s.toNNReal t.toNNReal) =
      ∫ s in 0..T, ∫ y, u y * P.occupationPotential v (T - s) y ∂P.realizedTransition s.toNNReal x := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    exact P.occupationPair_integral_potential x u v hs.1 hs.2
  exact (P.occupation_product_kac_triangle hκ x f g hT).trans
    (congrArg₂ (· + ·) (he f g) (he g f))

theorem GraphShiftedContactOperatorProblem.occupation_difference_square_potential
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : GraphContinuousPath P.geometry,
      ((∫ s in 0..T, f (p s.toNNReal)) - (∫ s in 0..T, g (p s.toNNReal))) ^ 2
        ∂P.continuousPathLaw hκ x) =
      2 * ∫ s in 0..T, ∫ y, (f - g) y * P.occupationPotential (f - g) (T - s) y
        ∂P.realizedTransition s.toNNReal x := by
  have he : (∫ s in 0..T, ∫ t in s..T,
      markovOccupationPair P.realizedTransition x (f - g) (f - g) s.toNNReal t.toNNReal) =
      ∫ s in 0..T, ∫ y, (f - g) y * P.occupationPotential (f - g) (T - s) y
        ∂P.realizedTransition s.toNNReal x := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    exact P.occupationPair_integral_potential x (f - g) (f - g) hs.1 hs.2
  exact (P.occupation_difference_square_kac_triangle hκ x f g hT).trans (congrArg (2 * ·) he)

end TimeTraps.Analysis
