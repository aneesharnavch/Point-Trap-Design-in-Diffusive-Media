module

public import TimeTraps.Analysis.IntervalSlopeUniquenessRegularity

@[expose] public section

/-! The natural strong certificate for continuous conductance is an AC/L2
flux, rather than a derivative of the conductance. It supplies the actual
classical state derivative and both one-sided derivatives. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

structure IntervalFluxRegularity (u j g p : ℝ → ℝ) (l r : ℝ) : Prop where
  state_energy : IntervalEnergy u l r
  flux_energy : IntervalEnergy j l r
  flux_ae : (fun x => p x * deriv u x) =ᵐ[volume.restrict (Ioo l r)] j
  source_ae : deriv j =ᵐ[volume.restrict (Ioo l r)] g

variable {u j g p : ℝ → ℝ} {l r : ℝ}

theorem IntervalFluxRegularity.derivative_ae (h : IntervalFluxRegularity u j g p l r)
    (hp : ∀ x ∈ Icc l r, p x ≠ 0) :
    deriv u =ᵐ[volume.restrict (Ioo l r)] (fun x => j x / p x) := by
  filter_upwards [h.flux_ae, ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx hm
  exact (eq_div_iff (hp x (Ioo_subset_Icc_self hm))).mpr (by simpa only [mul_comm] using hx)

theorem IntervalFluxRegularity.hasDerivAt (h : IntervalFluxRegularity u j g p l r)
    (hc : ContinuousOn p (Icc l r)) (hp : ∀ x ∈ Icc l r, p x ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo l r) : HasDerivAt u (j x / p x) x := by
  apply intervalEnergy_hasDerivAt_of_ae_deriv h.state_energy _ (h.derivative_ae hp) hx
  exact (by simpa only [uIcc_of_le (hx.1.trans hx.2).le] using h.flux_energy.continuousOn : ContinuousOn j (Icc l r)).div hc hp

theorem IntervalFluxRegularity.hasDerivWithinAt_left (h : IntervalFluxRegularity u j g p l r)
    (hlr : l < r) (hc : ContinuousOn p (Icc l r)) (hp : ∀ x ∈ Icc l r, p x ≠ 0) :
    HasDerivWithinAt u (j l / p l) (Ici l) l := by
  apply intervalEnergy_hasDerivWithinAt_left_of_ae_deriv h.state_energy hlr _ (h.derivative_ae hp)
  exact (by simpa only [uIcc_of_le hlr.le] using h.flux_energy.continuousOn : ContinuousOn j (Icc l r)).div hc hp

theorem IntervalFluxRegularity.hasDerivWithinAt_right (h : IntervalFluxRegularity u j g p l r)
    (hlr : l < r) (hc : ContinuousOn p (Icc l r)) (hp : ∀ x ∈ Icc l r, p x ≠ 0) :
    HasDerivWithinAt u (j r / p r) (Iic r) r := by
  apply intervalEnergy_hasDerivWithinAt_right_of_ae_deriv h.state_energy hlr _ (h.derivative_ae hp)
  exact (by simpa only [uIcc_of_le hlr.le] using h.flux_energy.continuousOn : ContinuousOn j (Icc l r)).div hc hp

theorem IntervalFluxRegularity.flux_hasDerivAt (h : IntervalFluxRegularity u j g p l r)
    (hg : ContinuousOn g (Icc l r)) {x : ℝ} (hx : x ∈ Ioo l r) : HasDerivAt j (g x) x :=
  intervalEnergy_hasDerivAt_of_ae_deriv h.flux_energy hg h.source_ae hx

end TimeTraps.Analysis
