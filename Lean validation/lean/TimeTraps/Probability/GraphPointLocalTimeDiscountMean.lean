module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountMartingale
public import TimeTraps.Analysis.GraphHeatPointResolventData

@[expose] public section

/-! The actual mean of the discounted total is the independently defined
heat point resolvent potential. Fubini is applied only after product
absolute integrability has been established. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTotal_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) :
    (∫ p, P.pointLocalTimeDiscountedTotal a α p ∂P.continuousPathLaw hκ x) =
      P.pointLocalTimeDiscountedPotential a α x := by
  let inst := P.continuousPathLaw_probability hκ x
  unfold pointLocalTimeDiscountedTotal pointLocalTimeDiscountedPotential
  rw [integral_const_mul]
  congr 1
  rw [← integral_integral_swap (P.pointLocalTimeDiscount_product_integrable hκ x a hα)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  rw [integral_const_mul, P.pointLocalTime_mean hκ x a H.toNNReal, Real.coe_toNNReal H hH.le]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    (∫ p, P.pointLocalTimeDiscountedTerminal a α t p ∂P.continuousPathLaw hκ x) =
      P.pointLocalTimeDiscountedPotential a α x := by
  let inst := P.continuousPathLaw_probability hκ x
  calc
    _ = ∫ p, (P.continuousPathLaw hκ x)[P.pointLocalTimeDiscountedTotal a α |
        graphContinuousNaturalFiltration P.geometry t] p ∂P.continuousPathLaw hκ x :=
      integral_congr_ae (P.pointLocalTimeDiscountedTerminal_condExp hκ x a hα t).symm
    _ = ∫ p, P.pointLocalTimeDiscountedTotal a α p ∂P.continuousPathLaw hκ x :=
      integral_condExp ((graphContinuousNaturalFiltration P.geometry).le t)
    _ = _ := P.pointLocalTimeDiscountedTotal_mean hκ x a hα

end TimeTraps.Analysis
