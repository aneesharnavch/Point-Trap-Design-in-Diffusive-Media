module

public import TimeTraps.Probability.BrownianLocalTimeSupportKernel

@[expose] public section

/-! On any event whose paths stay a fixed positive distance from a level
throughout a fixed finite time interval, the actual L2 Tanaka compensation
has zero increment almost everywhere. A subsequence of the checked L2
limit identifies the pointwise vanishing smooth increments. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaKernelDrift_increment_away_tendsto
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (a : ℝ) {S T : ℝ≥0} (hST : S ≤ T) {δ : ℝ} (hδ : 0 < δ) (ω : Ω)
    (haway : ∀ s ∈ Icc S T, δ ≤ |B s ω - a|) :
    Tendsto (fun n =>
      brownianItoDrift B (fun x => tanakaOccupationKernel (tanakaSmoothingScale n) (x - a)) T ω -
      brownianItoDrift B (fun x => tanakaOccupationKernel (tanakaSmoothingScale n) (x - a)) S ω)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n =>
    (tanakaSmoothingScale n ^ 2 / (2 * δ ^ 3)) * (T.val - S.val))
  · intro n
    simpa only [Real.norm_eq_abs] using brownianTanakaKernelDrift_increment_away_bound
      (tanakaSmoothingScale_pos n) hδ hjoint a hST ω haway
  · simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_mul] using
      ((tanakaSmoothingScale_tendsto.pow 2).div_const (2 * δ ^ 3)).mul_const (T.val - S.val)

theorem brownianTanakaCompensation_eq_on_away_event
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (a : ℝ) {S T : ℝ≥0} (hST : S ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (E : Set Ω) (haway : ∀ ω ∈ E, ∀ s ∈ Icc S T, δ ≤ |B s ω - a|) :
    ∀ᵐ ω ∂P, ω ∈ E → brownianTanakaCompensation hB hBm hjoint a T ω =
      brownianTanakaCompensation hB hBm hjoint a S ω := by
  let X := brownianTanakaSmoothCompensation hB hBm hjoint a S
  let Y := brownianTanakaSmoothCompensation hB hBm hjoint a T
  let U := brownianTanakaCompensation hB hBm hjoint a S
  let V := brownianTanakaCompensation hB hBm hjoint a T
  let A : ℕ → Lp ℝ 2 P := fun n => Y n - X n
  have hlim : Tendsto A atTop (𝓝 (V - U)) :=
    (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a T).sub
      (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a S)
  obtain ⟨b, hb, hsubseq⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ ω ∂P, ∀ n, A n ω =
      brownianItoDrift B (fun x => tanakaOccupationKernel (tanakaSmoothingScale n) (x - a)) T ω -
      brownianItoDrift B (fun x => tanakaOccupationKernel (tanakaSmoothingScale n) (x - a)) S ω := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_sub (Y n) (X n),
      brownianTanakaSmoothCompensation_kernel_coe hB hBm hjoint a T n,
      brownianTanakaSmoothCompensation_kernel_coe hB hBm hjoint a S n] with ω hd hy hx
    change (Y n - X n) ω = _
    rw [hd, Pi.sub_apply, hy, hx]
  filter_upwards [hsubseq, hcoe, Lp.coeFn_sub V U] with ω hω he hd
  intro hE
  have hz := (brownianTanakaKernelDrift_increment_away_tendsto hjoint a hST hδ ω
    (haway ω hE)).comp hb.tendsto_atTop
  have hz' : Tendsto (fun n => A (b n) ω) atTop (𝓝 0) := by
    simpa only [he, Function.comp_def] using hz
  have heq : (V - U) ω = 0 := tendsto_nhds_unique hω hz'
  rw [hd, Pi.sub_apply] at heq
  exact sub_eq_zero.mp heq

end TimeTraps.Probability
