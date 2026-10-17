module

public import TimeTraps.Probability.GraphPhysicalLocalTimePath
public import TimeTraps.Probability.GraphPointLocalTimeNormalization
public import TimeTraps.Probability.GraphPhysicalSpeedIndependence

@[expose] public section

/-! Physical local time has finite second moment at each time by the
deterministic inverse-clock bound and the actual reference second
moment. Its value is independent of the auxiliary positive vertex speed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    MemLp (P.physicalLocalTime b hb a T) 2 (P.continuousPathLaw hκ x) := by
  have hm : AEStronglyMeasurable (P.physicalLocalTime b hb a T) (P.continuousPathLaw hκ x) :=
    ((P.physicalLocalTime_stronglyAdapted b hb a T).mono
      ((P.geometry.physicalFiltration b hb).le T)).aestronglyMeasurable
  apply (P.pointLocalTime_memLp hκ x a (T / P.geometry.physicalSpeedLower b hb)).mono' hm
  filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp
  rw [P.physicalLocalTime_apply, hp, hp, Real.norm_eq_abs,
    abs_of_nonneg (P.pointLocalTimePath_nonneg a p _)]
  exact P.pointLocalTimePath_monotone a p (P.geometry.physicalInverseClock_bounds b hb T p).2

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    Integrable (P.physicalLocalTime b hb a T) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (P.physicalLocalTime_memLp hκ b hb x a T).integrable (by norm_num)

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_vertex_value_independent
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
      (a : GraphRealization P.geometry) (t : ℝ≥0),
      P.physicalLocalTime b hb a t p = P.physicalLocalTime c hc a t p := by
  filter_upwards [P.physicalInverseClock_vertex_value_independent hκ x] with p hp
  intro b c hb hc a t
  simp only [P.physicalLocalTime_apply, hp b c hb hc t]

end TimeTraps.Analysis
