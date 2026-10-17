module

public import TimeTraps.Analysis.TanakaOccupationKernelFubiniBound

@[expose] public section

/-! Fubini for the actual Tanaka kernel along measurable paths. The
level weight is any scalar L1 function, and the time measure is any
finite measure. The finite-horizon ordinary time integral is a direct
specialization. No occupation identity is used as a premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem tanakaOccupationKernel_average_recenter (ε : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    (∫ a, g a * tanakaOccupationKernel ε (x - a)) =
      ∫ y, tanakaOccupationKernel ε y * g (x - y) := by
  have he := integral_sub_left_eq_self
    (fun a => g a * tanakaOccupationKernel ε (x - a)) volume x
  simpa only [sub_sub_cancel, mul_comm] using he.symm

theorem tanakaOccupationKernel_path_pairing_integrable
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) {b : S → ℝ} (hb : Measurable b)
    {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun a => g a * ∫ s, tanakaOccupationKernel ε (b s - a) ∂μ) := by
  simpa only [integral_const_mul] using
    (tanakaOccupationKernel_path_integrable μ hε hb hg).integral_prod_left

theorem tanakaOccupationKernel_path_average_integrable
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) {b : S → ℝ} (hb : Measurable b)
    {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun s => ∫ y, tanakaOccupationKernel ε y * g (b s - y)) μ := by
  simpa only [tanakaOccupationKernel_average_recenter] using
    (tanakaOccupationKernel_path_integrable μ hε hb hg).integral_prod_right

theorem tanakaOccupationKernel_path_fubini
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) {b : S → ℝ} (hb : Measurable b)
    {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ a, g a * ∫ s, tanakaOccupationKernel ε (b s - a) ∂μ) =
      ∫ s, (∫ y, tanakaOccupationKernel ε y * g (b s - y)) ∂μ := by
  calc
    _ = ∫ a, ∫ s, g a * tanakaOccupationKernel ε (b s - a) ∂μ := by
      simp only [integral_const_mul]
    _ = ∫ s, (∫ a, g a * tanakaOccupationKernel ε (b s - a)) ∂μ :=
      integral_integral_swap (tanakaOccupationKernel_path_integrable μ hε hb hg)
    _ = _ := by simp only [tanakaOccupationKernel_average_recenter]

theorem tanakaOccupationKernel_time_fubini {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    {b : ℝ → ℝ} (hb : Measurable b) {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ a, g a * ∫ s in (0 : ℝ)..T, tanakaOccupationKernel ε (b s - a)) =
      ∫ s in (0 : ℝ)..T, ∫ y, tanakaOccupationKernel ε y * g (b s - y) := by
  simp only [intervalIntegral.integral_of_le hT]
  exact tanakaOccupationKernel_path_fubini (volume.restrict (Ioc 0 T)) hε hb hg

end TimeTraps.Analysis
