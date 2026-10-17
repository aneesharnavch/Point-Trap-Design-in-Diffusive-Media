module

public import TimeTraps.Analysis.CompactSpectralEnumeration
public import TimeTraps.Analysis.GeneralIntervalPointPositive
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-! The actual finite-interval L2 space is infinite-dimensional: polynomial
evaluation embeds all real polynomials linearly into it. Consequently
every checked finite-interval point-contact inverse has a naturally enumerated,
nondecreasing reciprocal spectrum diverging to infinity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Polynomial IntervalSobolevSpace Filter
open scoped Topology

variable {l r : ℝ}

noncomputable def intervalPolynomialL2 (hlr : l < r) : ℝ[X] →ₗ[ℝ] IntervalSobolevL2 l r :=
  (continuousL2 hlr).toLinearMap.comp
    (Polynomial.toContinuousMapOnAlgHom (Icc l r)).toLinearMap

theorem intervalPolynomialL2_injective (hlr : l < r) : Function.Injective (intervalPolynomialL2 hlr) := by
  intro p q hpq
  have hae : (fun x => p.eval x) =ᵐ[volume.restrict (Ioo l r)] fun x => q.eval x := by
    filter_upwards [continuousL2_ae hlr (p.toContinuousMapOn (Icc l r)),
      continuousL2_ae hlr (q.toContinuousMapOn (Icc l r)),
      ae_restrict_mem measurableSet_Ioo] with x hp hq hx
    have he := congrArg (fun f : IntervalSobolevL2 l r => f x) hpq
    change (continuousL2 hlr (p.toContinuousMapOn (Icc l r))) x =
      (continuousL2 hlr (q.toContinuousMapOn (Icc l r))) x at he
    rw [hp, hq, projIcc_of_mem hlr.le (Ioo_subset_Icc_self hx)] at he
    exact he
  have hpoint : EqOn (fun x => p.eval x) (fun x => q.eval x) (Ioo l r) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (by fun_prop) (by fun_prop)
  exact p.eq_of_infinite_eval_eq q ((Set.Ioo_infinite hlr).mono hpoint)

theorem intervalL2_not_finiteDimensional (hlr : l < r) : ¬FiniteDimensional ℝ (IntervalSobolevL2 l r) := by
  intro hf
  let := hf
  let : FiniteDimensional ℝ ℝ[X] :=
    FiniteDimensional.of_injective (intervalPolynomialL2 hlr) (intervalPolynomialL2_injective hlr)
  exact Module.Finite.not_linearIndependent_of_infinite (Polynomial.basisMonomials ℝ)
    (Polynomial.basisMonomials ℝ).linearIndependent

variable {ι : Type*} [Fintype ι]

theorem IntervalPointProblem.infinite_spectralIndex (P : IntervalPointProblem ι l r) :
    Infinite (CompactSpectralIndex P.inverse) :=
  P.compactPositiveInverse.infinite_spectralIndex (intervalL2_not_finiteDimensional P.interval_pos)

noncomputable def IntervalPointProblem.spectralEnumeration (P : IntervalPointProblem ι l r) :
    ℕ ≃ CompactSpectralIndex P.inverse := by
  letI := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration

theorem IntervalPointProblem.spectralEnumeration_monotone (P : IntervalPointProblem ι l r) :
    Monotone (fun n => (P.spectralEnumeration n).1⁻¹) := by
  let := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration_monotone

theorem IntervalPointProblem.spectralEnumeration_tendsto (P : IntervalPointProblem ι l r) :
    Tendsto (fun n => (P.spectralEnumeration n).1⁻¹) atTop atTop := by
  let := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration_tendsto

end TimeTraps.Analysis
