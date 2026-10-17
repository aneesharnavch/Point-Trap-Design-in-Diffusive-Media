module

public import TimeTraps.Probability.OccupationPotentialCauchyData
public import TimeTraps.Probability.GraphConservativeOccupationPotential

@[expose] public section

/-! Uniform finite-time potential error controls the actual mean-square
error of nonnegative graph occupation approximants. All kernel/time
integrability comes from the proved original semigroup. -/

namespace TimeTraps.Analysis

open MeasureTheory Set TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationPotential_difference_pair_bound
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (f g : C(GraphRealization P.geometry, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) {T s ε : ℝ} (hs : s ∈ Icc 0 T)
    (he : ∀ r ∈ Icc 0 T, ∀ y, |P.occupationPotential (f - g) r y| ≤ ε) :
    (∫ y, (f - g) y * P.occupationPotential (f - g) (T - s) y
      ∂P.realizedTransition s.toNNReal x) ≤ ε * P.realizedFeller s.toNNReal (f + g) x := by
  rw [P.realizedFeller_apply]
  exact integral_occupationDifference_mul_le (P.realizedTransition s.toNNReal x) f g
    (P.occupationPotential (f - g) (T - s)) hf hg
    (he (T - s) ⟨sub_nonneg.mpr hs.2, sub_le_self _ hs.1⟩)
    (P.occupationPotential_kernelPair_integrable s.toNNReal x (f - g) (f - g) (T - s))
    (P.realizedFeller_integrable s.toNNReal (f + g) x)

theorem GraphShiftedContactOperatorProblem.occupationPotential_difference_time_bound
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (f g : C(GraphRealization P.geometry, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) {T ε : ℝ} (hT : 0 ≤ T)
    (he : ∀ r ∈ Icc 0 T, ∀ y, |P.occupationPotential (f - g) r y| ≤ ε) :
    (∫ s in 0..T, ∫ y, (f - g) y * P.occupationPotential (f - g) (T - s) y
      ∂P.realizedTransition s.toNNReal x) ≤ ε * P.occupationPotential (f + g) T x := by
  rw [P.occupationPotential_apply, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hT
    ((P.occupationPotential_kernelPair_continuous x (f - g) (f - g) T).intervalIntegrable 0 T)
    (((P.realizedFeller_observation_continuous (f + g) x).const_mul ε).intervalIntegrable 0 T)
  exact fun s hs => P.occupationPotential_difference_pair_bound x f g hf hg hs he

theorem GraphShiftedContactOperatorProblem.occupation_difference_square_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) {T ε : ℝ} (hT : 0 ≤ T)
    (he : ∀ r ∈ Icc 0 T, ∀ y, |P.occupationPotential (f - g) r y| ≤ ε) :
    (∫ p : GraphContinuousPath P.geometry,
      ((∫ s in 0..T, f (p s.toNNReal)) - (∫ s in 0..T, g (p s.toNNReal))) ^ 2
        ∂P.continuousPathLaw hκ x) ≤ 2 * ε * P.occupationPotential (f + g) T x := by
  rw [P.occupation_difference_square_potential hκ x f g hT, mul_assoc]
  exact mul_le_mul_of_nonneg_left (P.occupationPotential_difference_time_bound x f g hf hg hT he)
    zero_le_two

end TimeTraps.Analysis
