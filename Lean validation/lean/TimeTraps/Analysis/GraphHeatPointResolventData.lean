module

public import TimeTraps.Analysis.GraphHeatPointPotentialJoint

@[expose] public section

/-! The discounted point potential is defined from the actual graph
heat point potential, before its elliptic identification. This is the
same quantity used by the discounted local-time martingale. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (q : ℝ)
    (x : GraphRealization P.geometry) : ℝ :=
  q * ∫ H in Ioi (0 : ℝ), Real.exp (-(q * H)) * P.realizedHeatPointPotential x a H

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (a x : GraphRealization P.geometry) (q : ℝ) :
    P.pointLocalTimeDiscountedPotential a q x = P.pointLocalTimeDiscountedPotential x q a := by
  unfold pointLocalTimeDiscountedPotential
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun H => by
    dsimp only
    rw [P.realizedHeatPointPotential_symmetric])

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a x : GraphRealization P.geometry)
    {q : ℝ} (hq : 0 ≤ q) : 0 ≤ P.pointLocalTimeDiscountedPotential a q x := by
  obtain ⟨_, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  apply mul_nonneg hq
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  exact mul_nonneg (Real.exp_pos _).le (hb H hH.le x a).2.1

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_measurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (q : ℝ) :
    Measurable (P.pointLocalTimeDiscountedPotential a q) := by
  have hp : Continuous (fun z : GraphRealization P.geometry × ℝ => ((z.1, a), z.2)) :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hU := P.realizedHeatPointPotential_joint_continuous.comp hp
  have hm : Measurable (fun z : GraphRealization P.geometry × ℝ =>
      Real.exp (-(q * z.2)) * P.realizedHeatPointPotential z.1 a z.2) :=
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_snd).neg)).mul hU).measurable
  exact (hm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))).measurable.const_mul q

end TimeTraps.Analysis
