module

public import TimeTraps.Probability.GraphPointLocalTimeRevuzData
public import TimeTraps.Analysis.GraphHeatPointPotentialRevuz

@[expose] public section

/-! Literal Revuz normalization of the canonical graph point contact
measure relative to unnormalized ordinary length. Both nested integrals
are genuine; every graph point, including every vertex, is retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_length_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    Integrable (fun x => f x * ∫ p, P.pointLocalTimeContactIntegral a g T p ∂P.continuousPathLaw hκ x)
      P.geometry.lengthMeasure := by
  apply ((P.realizedHeatPointPotential_source_integrable f a T).const_mul (g a)).congr
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [P.pointLocalTimeContactIntegral_mean hκ x a g T]
  ring

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_length_pairing
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    (∫ x, f x * (∫ p, P.pointLocalTimeContactIntegral a g T p ∂P.continuousPathLaw hκ x)
      ∂P.geometry.lengthMeasure) = g a * P.occupationPotential f T a := by
  calc
    _ = ∫ x, g a * (f x * P.realizedHeatPointPotential x a T) ∂P.geometry.lengthMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [P.pointLocalTimeContactIntegral_mean hκ x a g T]
      ring
    _ = _ := by
      rw [integral_const_mul, P.realizedHeatPointPotential_source_pairing f a T.coe_nonneg]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_revuz
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    (g : GraphRealization P.geometry → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x, f x *
      (∫ p, P.pointLocalTimeContactIntegral a g t.toNNReal p ∂P.continuousPathLaw hκ x)
        ∂P.geometry.lengthMeasure) (𝓝[>] 0) (𝓝 (f a * g a)) := by
  have h := (P.realizedHeatPointPotential_source_shortTime f a).const_mul (g a)
  rw [mul_comm (g a) (f a)] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [P.pointLocalTimeContactIntegral_length_pairing hκ a f g t.toNNReal,
    P.realizedHeatPointPotential_source_pairing f a (le_of_lt ht), Real.coe_toNNReal t (le_of_lt ht)]
  ring

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_length_mass
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (T : ℝ≥0) :
    (∫ x, (∫ p, P.pointLocalTimeContactIntegral a (fun _ => 1) T p ∂P.continuousPathLaw hκ x)
      ∂P.geometry.lengthMeasure) = T.val := by
  have h := P.pointLocalTimeContactIntegral_length_pairing hκ a
    (ContinuousMap.const _ (1 : ℝ)) (fun _ => 1) T
  simp only [ContinuousMap.const_apply, one_mul] at h
  rw [h, P.occupationPotential_apply]
  simp only [P.realizedFeller_one hκ, ContinuousMap.const_apply,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rfl

end TimeTraps.Analysis
