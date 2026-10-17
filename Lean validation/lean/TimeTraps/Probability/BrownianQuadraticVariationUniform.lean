module

public import TimeTraps.Probability.BrownianQuadraticVariationStoppedAlmostSure
public import TimeTraps.Probability.DyadicQuadraticVariationApproximation

@[expose] public section

/-! Actual Brownian stopped dyadic quadratic variation converges almost
surely, along the whole dyadic sequence, uniformly over a compact time
interval. The compact horizon is fixed before the exceptional event;
one common event is also supplied for any countable list of horizons.
Only the Brownian predicate's almost-sure path continuity is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianStoppedDyadicPathQV_ae_uniform (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (stoppedDyadicPathQV (fun t => B t ω) T)
      (fun s => s.val) atTop (Icc 0 T) := by
  filter_upwards [hB.cont, brownianStoppedDyadicQV_grid_ae_tendsto hB.toIsPreBrownianReal T]
    with ω hcont hgrid
  exact stoppedDyadicPathQV_uniform_of_grid (fun t => B t ω) T hcont.continuousOn hgrid

theorem brownianStoppedDyadicQV_ae_uniform (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n s => brownianStoppedDyadicQV B T n s ω)
      (fun s => s.val) atTop (Icc 0 T) :=
  brownianStoppedDyadicPathQV_ae_uniform hB T

theorem brownianStoppedDyadicQV_countable_horizons_ae_uniform
    (hB : IsBrownianReal B P) (T : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      TendstoUniformlyOn (fun n s => brownianStoppedDyadicQV B (T k) n s ω)
        (fun s => s.val) atTop (Icc 0 (T k)) :=
  ae_all_iff.mpr (fun k => brownianStoppedDyadicQV_ae_uniform hB (T k))

theorem brownianDyadicPath_qv_ae_uniform (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      TendstoUniformlyOn (fun n s => brownianStoppedDyadicQV brownianDyadicPath T n s ω)
        (fun s => s.val) atTop (Icc 0 T) :=
  brownianStoppedDyadicQV_ae_uniform brownianDyadicPath_isBrownianReal T

end TimeTraps.Probability
