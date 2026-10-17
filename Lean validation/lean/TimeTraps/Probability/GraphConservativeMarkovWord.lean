module

public import TimeTraps.Probability.GraphConservativeMarkovWordData

@[expose] public section

/-! Full finite future words follow from the actual one-state stopping law
by conditional pull-out and the tower property. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.markovCylinder_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry)
      (fun p => (τ p : WithTop ℝ≥0))) :
    (P.continuousPathLaw hκ x)[(fun p => graphMarkovCylinder P.geometry w (τ p) p) |
      hτ.measurableSpace] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => P.markovCylinderKernel w (p (τ p))) := by
  let inst := P.continuousPathLaw_probability hκ x
  induction w generalizing τ with
  | nil =>
      simp only [graphMarkovCylinder, GraphShiftedContactOperatorProblem.markovCylinderKernel,
        ContinuousMap.one_apply, condExp_const hτ.measurableSpace_le]
      exact EventuallyEq.rfl
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      have hσ := finiteStoppingTime_add hτ h
      have hle : hτ.measurableSpace ≤ hσ.measurableSpace := by
        apply hτ.measurableSpace_mono hσ
        intro p
        change (τ p : WithTop ℝ≥0) ≤ ((τ p + h : ℝ≥0) : WithTop ℝ≥0)
        exact WithTop.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)
      have hfg : Integrable
          ((fun p => f (p (τ p + h))) *
            (fun p => graphMarkovCylinder P.geometry w (τ p + h) p)) (P.continuousPathLaw hκ x) :=
        P.markovCylinder_stopped_integrable hκ x ((h, f) :: w) hτ
      have hce : (P.continuousPathLaw hκ x)[
          (fun p => graphMarkovCylinder P.geometry ((h, f) :: w) (τ p) p) |
          hσ.measurableSpace] =ᵐ[P.continuousPathLaw hκ x]
          (fun p => (f * P.markovCylinderKernel w) (p (τ p + h))) := by
        exact (condExp_mul_of_stronglyMeasurable_left
          (continuousObservation_stopped_stronglyMeasurable
            (fun t (p : GraphContinuousPath P.geometry) => f (p t))
            (graphObservation_stronglyAdapted P.geometry f)
            (fun p => f.continuous.comp p.continuous) hσ) hfg
          (P.markovCylinder_stopped_integrable hκ x w hσ)).trans
          (((EventuallyEq.rfl).mul (ih hσ)).trans (Eventually.of_forall (fun _ => rfl)))
      calc
        _ =ᵐ[P.continuousPathLaw hκ x] (P.continuousPathLaw hκ x)[
            (P.continuousPathLaw hκ x)[
              (fun p => graphMarkovCylinder P.geometry ((h, f) :: w) (τ p) p) |
              hσ.measurableSpace] | hτ.measurableSpace] :=
          (condExp_condExp_of_le hle hσ.measurableSpace_le).symm
        _ =ᵐ[P.continuousPathLaw hκ x] (P.continuousPathLaw hκ x)[
            (fun p => (f * P.markovCylinderKernel w) (p (τ p + h))) | hτ.measurableSpace] :=
          condExp_congr_ae hce
        _ =ᵐ[P.continuousPathLaw hκ x] _ :=
          P.continuousPathLaw_strongMarkov hκ x (f * P.markovCylinderKernel w) h hτ

end TimeTraps.Analysis
