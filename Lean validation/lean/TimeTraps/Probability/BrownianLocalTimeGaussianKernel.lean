module

public import TimeTraps.Probability.BrownianTanakaSmoothOccupation
public import TimeTraps.Probability.BrownianOccupationL1TimeKernel
public import TimeTraps.Analysis.TanakaOccupationKernelAverage

@[expose] public section

/-! Gaussian expectations of the actual smooth Tanaka kernel are kernel
averages of the Gaussian density. The integrable Gaussian peak controls
their time integrals uniformly as the smoothing scale tends to zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem gaussian_tanaka_kernel_integral {ε : ℝ} (_hε : 0 < ε)
    (m a : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∫ z, tanakaOccupationKernel ε (z - a) ∂gaussianReal m v) =
      ∫ y, tanakaOccupationKernel ε y * gaussianPDFReal m v (a - y) := by
  rw [integral_gaussianReal_eq_integral_smul hv.ne']
  calc
    _ = ∫ z, gaussianPDFReal m v z * tanakaOccupationKernel ε (a - z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [show a - z = -(z - a) by ring, tanakaOccupationKernel_even]
      rfl
    _ = _ := tanakaOccupationKernel_average_recenter ε (gaussianPDFReal m v) a

theorem gaussian_tanaka_kernel_average_bound {ε : ℝ} (hε : 0 < ε)
    (m a : ℝ) (v : ℝ≥0) :
    |∫ y, tanakaOccupationKernel ε y * gaussianPDFReal m v (a - y)| ≤
      (Real.sqrt (2 * Real.pi * v))⁻¹ :=
  tanakaOccupationKernel_average_bound hε (measurable_gaussianPDFReal m v)
    (fun y => by
      rw [abs_of_nonneg (gaussianPDFReal_nonneg m v y)]
      exact gaussianPDFReal_le_peak m v y) a

theorem gaussian_tanaka_kernel_average_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (m a : ℝ) (v : ℝ≥0) :
    Tendsto (fun n => ∫ y, tanakaOccupationKernel (ε n) y * gaussianPDFReal m v (a - y))
      atTop (𝓝 (gaussianPDFReal m v a)) := by
  apply tanakaOccupationKernel_average_tendsto hε hεlim (measurable_gaussianPDFReal m v)
    (fun y => by
      rw [abs_of_nonneg (gaussianPDFReal_nonneg m v y)]
      exact gaussianPDFReal_le_peak m v y)
  unfold gaussianPDFReal
  fun_prop

theorem gaussianPDFReal_time_intervalIntegrable (m a : ℝ) (T : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => gaussianPDFReal m s.toNNReal a) volume 0 T.val := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
    (brownianOccupationL1Majorant_intervalIntegrable T.val)
  apply hi.mono' (by fun_prop : Measurable (fun s : ℝ => gaussianPDFReal m s.toNNReal a)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg m s.toNNReal a),
    brownianOccupationL1Majorant_eq_peak hs.1.le]
  simpa only [Real.coe_toNNReal s hs.1.le] using gaussianPDFReal_le_peak m s.toNNReal a

theorem gaussian_tanaka_kernel_time_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0)) (m a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..T.val,
      ∫ y, tanakaOccupationKernel (ε n) y * gaussianPDFReal m s.toNNReal (a - y))
      atTop (𝓝 (∫ s in (0 : ℝ)..T.val, gaussianPDFReal m s.toNNReal a)) := by
  have hm (n : ℕ) : Measurable (fun p : ℝ × ℝ =>
      tanakaOccupationKernel (ε n) p.2 * gaussianPDFReal m p.1.toNNReal (a - p.2)) :=
    ((tanakaOccupationKernel_continuous (hε n)).measurable.comp measurable_snd).mul (by fun_prop)
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
    (brownianOccupationL1Majorant_intervalIntegrable T.val)
  have hd := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val))
    (F := fun n s => ∫ y, tanakaOccupationKernel (ε n) y * gaussianPDFReal m s.toNNReal (a - y))
    (f := fun s : ℝ => gaussianPDFReal m s.toNNReal a) brownianOccupationL1Majorant
    (fun n => ((hm n).stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ))).aestronglyMeasurable) hi
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, brownianOccupationL1Majorant_eq_peak hs.1.le]
      simpa only [Real.coe_toNNReal s hs.1.le] using
        gaussian_tanaka_kernel_average_bound (hε n) m a s.toNNReal)
    (Eventually.of_forall (fun s => gaussian_tanaka_kernel_average_tendsto hε hεlim m a s.toNNReal))
  convert hd using 1
  · funext n
    exact intervalIntegral.integral_of_le T.coe_nonneg
  · exact congrArg (fun z : ℝ => 𝓝 z) (intervalIntegral.integral_of_le T.coe_nonneg)

end TimeTraps.Probability
