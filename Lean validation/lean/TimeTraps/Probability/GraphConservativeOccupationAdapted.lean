module

public import TimeTraps.Probability.GraphConservativeOccupationPotentialMean
public import Mathlib.Probability.Process.Adapted

@[expose] public section

/-! A continuous adapted particle path has an adapted occupation prefix.
Joint measurability in the raw past sigma algebra is derived by clamping
the time parameter at the current deterministic time. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.occupation_prefix_stronglyMeasurable
    (P : GraphShiftedContactOperatorProblem V E)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (GraphContinuousPath P.geometry)))
    (hX : StronglyAdapted ℱ (fun t (p : GraphContinuousPath P.geometry) => p t))
    (f : C(GraphRealization P.geometry, ℝ)) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] (fun p : GraphContinuousPath P.geometry =>
      ∫ r in 0..t.val, f (p r.toNNReal)) := by
  have hm : @StronglyMeasurable (ℝ × GraphContinuousPath P.geometry) ℝ _
      (MeasurableSpace.prod inferInstance (ℱ t))
      (fun q => f (q.2 (min q.1.toNNReal t))) := by
    let : MeasurableSpace (GraphContinuousPath P.geometry) := ℱ t
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (r : ℝ) (p : GraphContinuousPath P.geometry) => f (p (min r.toNNReal t)))
    · intro p
      exact (f.continuous.comp p.continuous).comp (continuous_real_toNNReal.min continuous_const)
    · intro r
      exact f.continuous.comp_stronglyMeasurable ((hX (min r.toNNReal t)).mono (ℱ.mono (min_le_right _ _)))
  have he : (fun p : GraphContinuousPath P.geometry => ∫ r in 0..t.val, f (p r.toNNReal)) =
      (fun p => ∫ r in Ioc 0 t.val, f (p (min r.toNNReal t))) := by
    funext p
    apply (intervalIntegral.integral_of_le (f := fun r => f (p r.toNNReal)) t.coe_nonneg).trans
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hr.2
    rw [min_eq_left hrt]
  rw [he]
  let : MeasurableSpace (GraphContinuousPath P.geometry) := ℱ t
  exact hm.integral_prod_left' (μ := volume.restrict (Ioc 0 t.val))

end TimeTraps.Analysis
