module

public import TimeTraps.Probability.BrownianOccupationTimeConvergence
public import TimeTraps.Analysis.TanakaOccupationKernelParametric

@[expose] public section

/-! The normalized Tanaka kernel averages converge inside the genuine
ordinary time integral, for every path and in actual L2. This supplies
the time side of occupation approximation without an occupation premise. -/

namespace TimeTraps.Probability

open MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianOccupationKernel_time_memLp [IsFiniteMeasure P]
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ} (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    MemLp (brownianItoDrift B (fun x => ∫ y, tanakaOccupationKernel ε y * g (x - y)) T) 2 P :=
  brownianItoDrift_bounded_memLp (tanakaOccupationKernel_average_measurable hε hg)
    hjoint (tanakaOccupationKernel_average_bound hε hg hb) T

theorem brownianOccupationKernel_time_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {g : ℝ → ℝ} (hg : Continuous g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => brownianItoDrift B
      (fun x => ∫ y, tanakaOccupationKernel (ε n) y * g (x - y)) T ω) atTop
      (𝓝 (brownianItoDrift B g T ω)) :=
  brownianItoDrift_bounded_tendsto
    (fun n => tanakaOccupationKernel_average_measurable (hε n) hg.measurable) hjoint
    (fun n => tanakaOccupationKernel_average_bound (hε n) hg.measurable hb)
    (fun _ => tanakaOccupationKernel_average_tendsto hε hεlim hg.measurable hb hg.continuousAt) T ω

theorem brownianOccupationKernel_timeL2_tendsto [IsFiniteMeasure P]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {g : ℝ → ℝ} (hg : Continuous g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoDriftL2 B
      (fun x => ∫ y, tanakaOccupationKernel (ε n) y * g (x - y)) T
      (brownianOccupationKernel_time_memLp (P := P) (hε n) hg.measurable hjoint hb T)) atTop
      (𝓝 (brownianItoDriftL2 B g T (brownianItoDrift_bounded_memLp (P := P) hg.measurable hjoint hb T))) :=
  brownianItoDriftL2_bounded_tendsto
    (fun n => tanakaOccupationKernel_average_measurable (hε n) hg.measurable) hg.measurable hjoint
    (fun n => tanakaOccupationKernel_average_bound (hε n) hg.measurable hb) hb
    (fun _ => tanakaOccupationKernel_average_tendsto hε hεlim hg.measurable hb hg.continuousAt) T

theorem brownianDyadicOccupationKernel_timeL2_tendsto {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoDriftL2 brownianDyadicPath
      (fun x => ∫ y, tanakaOccupationKernel (tanakaSmoothingScale n) y * g (x - y)) T
      (brownianOccupationKernel_time_memLp (P := brownianDyadicMeasure)
        (tanakaSmoothingScale_pos n) hg.measurable brownianDyadicPath_jointly_measurable hb T)) atTop
      (𝓝 (brownianItoDriftL2 brownianDyadicPath g T
        (brownianItoDrift_bounded_memLp (P := brownianDyadicMeasure)
          hg.measurable brownianDyadicPath_jointly_measurable hb T))) :=
  brownianOccupationKernel_timeL2_tendsto tanakaSmoothingScale_pos tanakaSmoothingScale_tendsto
    hg brownianDyadicPath_jointly_measurable hb T

end TimeTraps.Probability
