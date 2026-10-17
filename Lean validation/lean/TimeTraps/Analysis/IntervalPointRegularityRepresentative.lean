module

public import TimeTraps.Analysis.IntervalEnergyLocal
public import TimeTraps.Analysis.IntervalSobolevRepresentation

@[expose] public section

/-! An AC function whose a.e. derivative has a continuous representative is
classically differentiable at every interior point.  The continuous slope
also supplies the two one-sided endpoint traces, without requiring forcing
values at endpoints. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

theorem intervalEnergy_primitive_of_ae_deriv {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l ≤ r)
    (hd : deriv u =ᵐ[volume.restrict (Ioo l r)] v) {x : ℝ} (hx : x ∈ Icc l r) :
    u x = u l + ∫ t in l..x, v t := by
  have hi : (∫ t in l..x, deriv u t) = ∫ t in l..x, v t := by
    simp only [intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    exact hd.filter_mono (ae_mono (Measure.restrict_mono_set volume (Ioo_subset_Ioo le_rfl hx.2)))
  have hu' := hu.absolutelyContinuous.mono (show uIcc l x ⊆ uIcc l r by
    rw [uIcc_of_le hx.1, uIcc_of_le hlr]
    exact Icc_subset_Icc le_rfl hx.2)
  rw [← hi, hu'.integral_deriv_eq_sub]
  ring

theorem intervalEnergy_hasDerivAt_of_ae_deriv {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hv : ContinuousOn v (Icc l r))
    (hd : deriv u =ᵐ[volume.restrict (Ioo l r)] v) {x : ℝ} (hx : x ∈ Ioo l r) :
    HasDerivAt u (v x) x := by
  have hp := (integral_primitive_hasDerivAt hv hx).const_add (u l)
  apply hp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact intervalEnergy_primitive_of_ae_deriv hu (hx.1.trans hx.2).le hd
    (Ioo_subset_Icc_self hy)

theorem intervalEnergy_deriv_left_trace {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hv : ContinuousOn v (Icc l r))
    (hd : deriv u =ᵐ[volume.restrict (Ioo l r)] v) :
    Tendsto (deriv u) (𝓝[>] l) (𝓝 (v l)) := by
  have hmem : Icc l r ∈ 𝓝[>] l := by
    filter_upwards [Ioo_mem_nhdsGT hlr] with x hx
    exact Ioo_subset_Icc_self hx
  have hc := (hv l (show l ∈ Icc l r from ⟨le_rfl, hlr.le⟩)).mono_left
    (nhdsWithin_le_of_mem hmem)
  apply hc.congr'
  filter_upwards [Ioo_mem_nhdsGT hlr] with x hx
  exact (intervalEnergy_hasDerivAt_of_ae_deriv hu hv hd hx).deriv.symm

theorem intervalEnergy_deriv_right_trace {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hv : ContinuousOn v (Icc l r))
    (hd : deriv u =ᵐ[volume.restrict (Ioo l r)] v) :
    Tendsto (deriv u) (𝓝[<] r) (𝓝 (v r)) := by
  have hmem : Icc l r ∈ 𝓝[<] r := by
    filter_upwards [Ioo_mem_nhdsLT hlr] with x hx
    exact Ioo_subset_Icc_self hx
  have hc := (hv r (show r ∈ Icc l r from ⟨hlr.le, le_rfl⟩)).mono_left
    (nhdsWithin_le_of_mem hmem)
  apply hc.congr'
  filter_upwards [Ioo_mem_nhdsLT hlr] with x hx
  exact (intervalEnergy_hasDerivAt_of_ae_deriv hu hv hd hx).deriv.symm

end TimeTraps.Analysis
