module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentWindow
public import TimeTraps.Probability.ReflectedInteriorOccupationMeasurable

@[expose] public section

/-! Spatial Fubini identifies the continuous local extension with the
original occupation density at each fixed time. Countably many dense
times are then placed on one event before extending any band identity. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedLocalTimeWindowVersion_density_spatial_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < L) (t : BrownianCompactTime T) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      (fun z => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω t)
        =ᵐ[volume.restrict (Icc l r)] foldedOccupationDensity L D x t.val ω := by
  have hlevel : ∀ᵐ z ∂volume.restrict (Icc l r), ∀ᵐ ω ∂brownianDyadicMeasure,
      reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω t =
        foldedOccupationDensity L D x t.val ω z := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    have hzI : z ∈ Ioo (0 : ℝ) L := ⟨hl.trans_le hz.1, hz.2.trans_lt hr⟩
    filter_upwards [reflectedLocalTimeSpatialVersion_fixed_level_all_times L hL D hD x T
        (reflectedSpatialWindowPoint L l r hl hlr hr z),
      reflectedInteriorOccupationCoefficient_density_all_times_ae L hL D hD x z hzI] with ω hv hd
    have he := hv t
    rw [reflectedSpatialWindowPoint_of_mem L l r hl hlr hr hz] at he
    exact he.trans (hd t.val)
  have hm : MeasurableSet {p : ℝ × (ℕ → ℝ) |
      reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr p.1 p.2 t =
        foldedOccupationDensity L D x t.val p.2 p.1} :=
    measurableSet_eq_fun (reflectedLocalTimeWindowVersion_jointlyMeasurable L hL D hD x T l r hl hlr hr t)
      (foldedOccupationDensity_timeSlice_jointlyMeasurable L D x t.val)
  exact (Measure.ae_ae_comm hm).mp hlevel

theorem reflectedLocalTimeWindowVersion_density_dense_times_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      (fun z => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω
        (denseSeq (BrownianCompactTime T) n)) =ᵐ[volume.restrict (Icc l r)]
          foldedOccupationDensity L D x (denseSeq (BrownianCompactTime T) n).val ω :=
  ae_all_iff.mpr (fun n => reflectedLocalTimeWindowVersion_density_spatial_ae L hL D hD x T l r hl hlr hr (denseSeq (BrownianCompactTime T) n))

end TimeTraps.Probability
