module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentWindowDensity
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentTestData

@[expose] public section

/-! One event gives the occupation identity for the spatially continuous
version, all compact times and every bounded Borel test supported in the
fixed interior window. Spatial Fubini precedes the dense-time extension. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedLocalTimeWindow_occupation_all_tests_times_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ g : ℝ → ℝ, Measurable g → ∀ M : ℝ,
      (∀ z, |g z| ≤ M) → (∀ z ∉ Icc l r, g z = 0) → ∀ t : BrownianCompactTime T,
        brownianItoDrift (foldedTrajectory L D x brownianDyadicPath) g t.val ω =
          reflectedLocalTimeWindowTestPath L hL D hD x T l r hl hlr hr g ω t := by
  filter_upwards [reflectedLocalTimeWindowVersion_density_dense_times_ae L hL D hD x T l r hl hlr hr,
    foldedOccupationDensity_bounded_occupation_all_times_ae] with ω hdense hocc g hg M hb hsupp
  have hc : Continuous (fun t : BrownianCompactTime T =>
      brownianItoDrift (foldedTrajectory L D x brownianDyadicPath) g t.val ω) :=
    (brownianItoDrift_bounded_continuous
      (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable)
      hg hb ω).comp continuous_subtype_val
  have he := (denseRange_denseSeq (BrownianCompactTime T)).equalizer hc
    (reflectedLocalTimeWindowTestPath L hL D hD x T l r hl hlr hr g ω).continuous (funext (fun n => ?_))
  · intro t
    exact congrFun he t
  · let t := denseSeq (BrownianCompactTime T) n
    have ho := hocc t.val L hL D hD x g hg M hb
    rw [Function.comp_apply, Function.comp_apply,
      reflectedLocalTimeWindowTestPath_apply L hL D hD x T l r hl hlr hr hg hb]
    calc
      _ = ∫ z, g z * foldedOccupationDensity L D x t.val ω z := ho.2.2.symm
      _ = ∫ z in Icc l r, g z * foldedOccupationDensity L D x t.val ω z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hsupp z hz, zero_mul])).symm
      _ = _ := integral_congr_ae ((hdense n).mono (fun z hz => congrArg (fun v : ℝ => g z * v) hz.symm))

end TimeTraps.Probability
