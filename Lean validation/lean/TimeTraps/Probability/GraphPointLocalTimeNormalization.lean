module

public import TimeTraps.Probability.GraphPointLocalTimePath
public import TimeTraps.Probability.GraphPointOccupationL2Unique
public import TimeTraps.Probability.GraphPointLocalTimeL2Properties

@[expose] public section

/-! The canonical continuous and raw-adapted graph local times represent
the independently constructed occupation L2 limits. Their integrability
and exact original heat-potential expectations are consequences. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_eq_L2_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    (fun p => P.pointLocalTimePath a p T) =ᵐ[P.continuousPathLaw hκ x] P.pointLocalTimeL2 hκ x a T := by
  let inst := P.continuousPathLaw_probability hκ x
  let F := fun n => P.occupationL2 hκ x (P.geometry.pointBump a (P.localTimeRadius n)) T
  have hLp : Tendsto F atTop (𝓝 (P.pointLocalTimeL2 hκ x a T)) :=
    P.pointLocalTimeL2_tendsto_sequence hκ x a T P.localTimeRadius_pos P.localTimeRadius_tendsto
  have hAE : ∀ᵐ p ∂P.continuousPathLaw hκ x, Tendsto (fun n => F n p) atTop
      (𝓝 (P.pointLocalTimePath a p T)) := by
    filter_upwards [P.localTimeApproximant_hasLimit_ae hκ x a,
      ae_all_iff.mpr (fun n => P.occupationL2_coe hκ x (P.geometry.pointBump a (P.localTimeRadius n)) T)]
      with p hp he
    simpa only [F, he, P.localTimeApproximant_apply, GraphShiftedContactOperatorProblem.pointLocalTimePath]
      using hp.eval_tendsto T
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable (F n)) hAE)
    (tendstoInMeasure_of_tendsto_Lp hLp)

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    MemLp (fun p => P.pointLocalTimePath a p T) 2 (P.continuousPathLaw hκ x) :=
  (Lp.memLp (P.pointLocalTimeL2 hκ x a T)).ae_eq (P.pointLocalTimePath_eq_L2_ae hκ x a T).symm

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    (∫ p, P.pointLocalTimePath a p T ∂P.continuousPathLaw hκ x) = P.realizedHeatPointPotential x a T :=
  (integral_congr_ae (P.pointLocalTimePath_eq_L2_ae hκ x a T)).trans (P.pointLocalTimeL2_mean hκ x a T)

theorem GraphShiftedContactOperatorProblem.pointLocalTime_eq_L2_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    P.pointLocalTime a T =ᵐ[P.continuousPathLaw hκ x] P.pointLocalTimeL2 hκ x a T := by
  have hp : P.pointLocalTime a T =ᵐ[P.continuousPathLaw hκ x] (fun p => P.pointLocalTimePath a p T) :=
    (P.pointLocalTime_eq_path_ae hκ x a).mono (fun _ h => h T)
  exact hp.trans (P.pointLocalTimePath_eq_L2_ae hκ x a T)

theorem GraphShiftedContactOperatorProblem.pointLocalTime_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    MemLp (P.pointLocalTime a T) 2 (P.continuousPathLaw hκ x) :=
  (Lp.memLp (P.pointLocalTimeL2 hκ x a T)).ae_eq (P.pointLocalTime_eq_L2_ae hκ x a T).symm

theorem GraphShiftedContactOperatorProblem.pointLocalTime_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    (∫ p, P.pointLocalTime a T p ∂P.continuousPathLaw hκ x) = P.realizedHeatPointPotential x a T :=
  (integral_congr_ae (P.pointLocalTime_eq_L2_ae hκ x a T)).trans (P.pointLocalTimeL2_mean hκ x a T)

end TimeTraps.Analysis
