module

public import TimeTraps.Probability.GraphPointOccupationL2
public import TimeTraps.Probability.RealL2LimitOrder
public import TimeTraps.Probability.GraphConservativeOccupationPotentialMean

@[expose] public section

/-! The constructed graph local-time classes are nonnegative and ordered
in time. Their expectations equal the actual original heat point
potential, fixing the ordinary-length normalization of the limit. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Probability TimeTraps.Graph
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationL2_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    (∫ p, P.occupationL2 hκ x f T p ∂P.continuousPathLaw hκ x) =
      P.occupationPotential f T x :=
  (integral_congr_ae (P.occupationL2_coe hκ x f T)).trans
    (P.occupation_mean_potential hκ x f T)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, 0 ≤ P.pointLocalTimeL2 hκ x a T p := by
  apply realL2_limit_nonneg_ae (P.pointLocalTimeL2_tendsto hκ x a T)
  intro n
  filter_upwards [P.occupationL2_coe hκ x (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) T] with p hp
  rw [hp]
  exact intervalIntegral.integral_nonneg T.coe_nonneg
    (fun s _ => P.geometry.pointBump_nonneg a (p s.toNNReal) _)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_mono
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, P.pointLocalTimeL2 hκ x a S p ≤ P.pointLocalTimeL2 hκ x a T p := by
  apply realL2_limit_le_ae (P.pointLocalTimeL2_tendsto hκ x a S) (P.pointLocalTimeL2_tendsto hκ x a T)
  intro n
  let f := P.geometry.pointBump a (1 / ((n : ℝ) + 1))
  filter_upwards [P.occupationL2_coe hκ x f S, P.occupationL2_coe hκ x f T] with p hS hT
  rw [hS, hT]
  exact intervalIntegral.integral_mono_interval le_rfl S.coe_nonneg (show (S : ℝ) ≤ T from hST)
    (Eventually.of_forall (fun s => P.geometry.pointBump_nonneg a (p s.toNNReal) _))
    (((f.continuous.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable 0 T)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    (∫ p, P.pointLocalTimeL2 hκ x a T p ∂P.continuousPathLaw hκ x) =
      P.realizedHeatPointPotential x a T := by
  let inst := P.continuousPathLaw_probability hκ x
  have ht := realL2_integral_continuous.continuousAt.tendsto.comp
    (P.pointLocalTimeL2_tendsto hκ x a T)
  simp only [Function.comp_def, P.occupationL2_mean] at ht
  apply tendsto_nhds_unique ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := P.occupationPotential_pointBump_compact_uniform T hε
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)] with n hn
  rw [Real.dist_eq]
  exact hd (1 / ((n : ℝ) + 1)) (by positivity) hn T ⟨T.coe_nonneg, le_rfl⟩ x a

end TimeTraps.Analysis
