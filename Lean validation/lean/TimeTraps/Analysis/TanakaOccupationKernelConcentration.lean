module

public import TimeTraps.Analysis.TanakaOccupationKernelMass

@[expose] public section

/-! Exact finite-interval and tail masses prove concentration of the
smooth occupation kernels at zero as the smoothing scale vanishes. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped Topology

theorem tanakaOccupationKernel_interval {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (∫ x in (-R)..R, tanakaOccupationKernel ε x) = R / tanakaSmoothAbs ε R := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => tanakaOccupationKernel_primitive hε x)
    ((tanakaOccupationKernel_continuous hε).intervalIntegrable (-R) R)
  rw [h, tanakaSmoothAbs_deriv_neg hε, tanakaSmoothAbs_deriv hε]
  ring

theorem tanakaOccupationKernel_Icc {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in Icc (-R) R, tanakaOccupationKernel ε x) = R / tanakaSmoothAbs ε R := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  exact tanakaOccupationKernel_interval hε R

theorem tanakaOccupationKernel_tail {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in (Icc (-R) R)ᶜ, tanakaOccupationKernel ε x) = 1 - R / tanakaSmoothAbs ε R := by
  rw [setIntegral_compl measurableSet_Icc (tanakaOccupationKernel_integrable hε),
    tanakaOccupationKernel_integral hε, tanakaOccupationKernel_Icc hε hR]

theorem tanakaOccupationKernel_tail_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => ∫ x in (Icc (-R) R)ᶜ, tanakaOccupationKernel (ε n) x) atTop (𝓝 0) := by
  have hq := (tendsto_const_nhds (x := R)).div
    (tanakaSmoothAbs_tendsto hlim R) (abs_ne_zero.mpr hR.ne')
  have ht : Tendsto (fun n => 1 - R / tanakaSmoothAbs (ε n) R) atTop (𝓝 (1 - R / |R|)) :=
    tendsto_const_nhds.sub hq
  have hz : 1 - R / |R| = 0 := by rw [abs_of_pos hR, div_self hR.ne', sub_self]
  rw [hz] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => (tanakaOccupationKernel_tail (hε n) hR.le).symm

theorem tanakaOccupationKernel_scale_tail_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => ∫ x in (Icc (-R) R)ᶜ, tanakaOccupationKernel (tanakaSmoothingScale n) x)
      atTop (𝓝 0) :=
  tanakaOccupationKernel_tail_tendsto tanakaSmoothingScale_pos tanakaSmoothingScale_tendsto hR

end TimeTraps.Analysis
