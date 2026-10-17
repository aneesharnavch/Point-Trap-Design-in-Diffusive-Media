module

public import TimeTraps.Analysis.CompactSpectralEnumeration
public import TimeTraps.Analysis.IntervalSobolevOperatorPositive
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-! The actual unit-interval L2 space is infinite-dimensional: polynomial
evaluation embeds all real polynomials linearly into it. Consequently
every checked unit point-contact inverse has a naturally enumerated,
nondecreasing reciprocal spectrum diverging to infinity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Polynomial IntervalSobolevSpace Filter
open scoped Topology

noncomputable def unitIntervalPolynomialL2 : ℝ[X] →ₗ[ℝ] UnitIntervalL2 :=
  (continuousL2 zero_lt_one).toLinearMap.comp
    (Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1)).toLinearMap

theorem unitIntervalPolynomialL2_injective : Function.Injective unitIntervalPolynomialL2 := by
  intro p q hpq
  have hae : (fun x => p.eval x) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x => q.eval x := by
    filter_upwards [continuousL2_ae zero_lt_one (p.toContinuousMapOn (Icc (0 : ℝ) 1)),
      continuousL2_ae zero_lt_one (q.toContinuousMapOn (Icc (0 : ℝ) 1)),
      ae_restrict_mem measurableSet_Ioo] with x hp hq hx
    have he := congrArg (fun f : UnitIntervalL2 => f x) hpq
    change (continuousL2 zero_lt_one (p.toContinuousMapOn (Icc (0 : ℝ) 1))) x =
      (continuousL2 zero_lt_one (q.toContinuousMapOn (Icc (0 : ℝ) 1))) x at he
    rw [hp, hq, projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hx)] at he
    exact he
  have hpoint : EqOn (fun x => p.eval x) (fun x => q.eval x) (Ioo (0 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (by fun_prop) (by fun_prop)
  exact p.eq_of_infinite_eval_eq q ((Set.Ioo_infinite zero_lt_one).mono hpoint)

theorem unitIntervalL2_not_finiteDimensional : ¬FiniteDimensional ℝ UnitIntervalL2 := by
  intro hf
  let := hf
  let : FiniteDimensional ℝ ℝ[X] :=
    FiniteDimensional.of_injective unitIntervalPolynomialL2 unitIntervalPolynomialL2_injective
  exact Module.Finite.not_linearIndependent_of_infinite (Polynomial.basisMonomials ℝ)
    (Polynomial.basisMonomials ℝ).linearIndependent

variable {ι : Type*} [Fintype ι]

theorem UnitPointProblem.infinite_spectralIndex (P : UnitPointProblem ι) :
    Infinite (CompactSpectralIndex P.inverse) :=
  P.compactPositiveInverse.infinite_spectralIndex unitIntervalL2_not_finiteDimensional

noncomputable def UnitPointProblem.spectralEnumeration (P : UnitPointProblem ι) :
    ℕ ≃ CompactSpectralIndex P.inverse := by
  letI := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration

theorem UnitPointProblem.spectralEnumeration_monotone (P : UnitPointProblem ι) :
    Monotone (fun n => (P.spectralEnumeration n).1⁻¹) := by
  let := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration_monotone

theorem UnitPointProblem.spectralEnumeration_tendsto (P : UnitPointProblem ι) :
    Tendsto (fun n => (P.spectralEnumeration n).1⁻¹) atTop atTop := by
  let := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration_tendsto

end TimeTraps.Analysis
