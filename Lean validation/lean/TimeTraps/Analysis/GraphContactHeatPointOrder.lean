module

public import TimeTraps.Analysis.GraphContactHeatSobolev
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! The positive-time physical representative preserves positivity and
the upper bound one at every closed-edge point, including vertices.
The upgrade from almost everywhere uses continuity of the H1 representative. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem graphContact_continuous_le_of_ae {l r : ℝ} (hlr : l < r) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc l r)) (hg : ContinuousOn g (Icc l r))
    (hfg : f ≤ᵐ[volume.restrict (Ioo l r)] g) :
    ∀ x ∈ Icc l r, f x ≤ g x := by
  have he : f =ᵐ[volume.restrict (Ioo l r)] (fun x => min (f x) (g x)) :=
    hfg.mono (fun _ hx => (min_eq_left hx).symm)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he
  have heq := Measure.eqOn_Icc_of_ae_eq volume hlr.ne he hf (hf.inf hg)
  intro x hx
  rw [heq hx]
  exact min_le_right _ _

theorem GraphContactOperatorProblem.heatPointEvaluation_nonneg (P : GraphContactOperatorProblem V E)
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

theorem GraphContactOperatorProblem.heatPointEvaluation_le_one (P : GraphContactOperatorProblem V E)
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

theorem GraphContactOperatorProblem.heatPointEvaluation_mono (P : GraphContactOperatorProblem V E)
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
