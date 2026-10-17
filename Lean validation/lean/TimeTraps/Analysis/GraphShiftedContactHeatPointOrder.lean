module

public import TimeTraps.Analysis.GraphShiftedContactHeatSobolev
public import TimeTraps.Analysis.GraphContactHeatPointOrder

@[expose] public section

/-! The positive-time physical representative preserves positivity and
the upper bound one at every closed-edge point, including vertices.
The upgrade from almost everywhere uses continuity of the H1 representative. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_nonneg (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) : 0 ≤ P.heatPointEvaluation t ht e x f := by
  have hc : ContinuousOn (P.operatorRep (P.heatSobolevL t ht f) e) (Icc 0 (P.geometry.length e)) := by
    have h := (graphSobolevRepresentative_energy P.geometry (P.heatSobolevL t ht f).val e).continuousOn
    change ContinuousOn (P.operatorRep (P.heatSobolevL t ht f) e) (uIcc 0 (P.geometry.length e)) at h
    simpa only [uIcc_of_le (P.geometry.length_pos e).le] using h
  apply graphContact_continuous_le_of_ae (P.geometry.length_pos e) continuousOn_const hc ?_ x x.property
  filter_upwards [P.heatSemigroup_nonneg_ae t f hf e, P.heatSobolevL_state_ae t ht f e] with y hy he
  rwa [← he]

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_le_one (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) : P.heatPointEvaluation t ht e x f ≤ 1 := by
  have hc : ContinuousOn (P.operatorRep (P.heatSobolevL t ht f) e) (Icc 0 (P.geometry.length e)) := by
    have h := (graphSobolevRepresentative_energy P.geometry (P.heatSobolevL t ht f).val e).continuousOn
    change ContinuousOn (P.operatorRep (P.heatSobolevL t ht f) e) (uIcc 0 (P.geometry.length e)) at h
    simpa only [uIcc_of_le (P.geometry.length_pos e).le] using h
  apply graphContact_continuous_le_of_ae (P.geometry.length_pos e) hc continuousOn_const ?_ x x.property
  filter_upwards [P.heatSemigroup_le_one_ae t f hf e, P.heatSobolevL_state_ae t ht f e] with y hy he
  rwa [← he]

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_mono (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, (f e) ≤ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] (g e))
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    P.heatPointEvaluation t ht e x f ≤ P.heatPointEvaluation t ht e x g := by
  have hnonneg : ∀ d, ∀ᵐ y ∂volume.restrict (Ioo 0 (P.geometry.length d)), 0 ≤ ((g - f) d) y := by
    intro d
    have he : (g - f) d = g d - f d := rfl
    rw [he]
    filter_upwards [hfg d, Lp.coeFn_sub (g d) (f d)] with y hy hs
    rw [hs, Pi.sub_apply]
    exact sub_nonneg.mpr hy
  have h := P.heatPointEvaluation_nonneg t ht (g - f) hnonneg e x
  rw [map_sub] at h
  exact sub_nonneg.mp h

end TimeTraps.Analysis
