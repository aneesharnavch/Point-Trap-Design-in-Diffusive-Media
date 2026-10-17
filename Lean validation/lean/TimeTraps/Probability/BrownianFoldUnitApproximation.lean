module

public import TimeTraps.Probability.BrownianFoldUnitStep
public import TimeTraps.Probability.BrownianFoldSlopeTimeGridL2

@[expose] public section

/-! The unit-valued left-grid process has the same product-L² limit as
the original fold slope. At time zero the corner convention is retained;
almost-everywhere convergence uses only positive-time corner exclusion. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldUnitTimeGrid_measurable (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) :
    Measurable (brownianFoldUnitTimeGrid B L x σ T n) := by
  unfold brownianFoldUnitTimeGrid brownianSquareStepProcess
  apply Finset.measurable_sum
  intro i _
  exact brownianElementaryProcess_measurable _ _ ((reflectedFoldUnitSlope_measurable L hL).comp
    (measurable_const.add (measurable_const.mul (hBm _))))

theorem brownianFoldUnitTimeGrid_abs (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    |brownianFoldUnitTimeGrid B L x σ T n p| = brownianIntervalIndicator 0 T p.1 := by
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hp
    change |brownianSquareStepProcess _ T n p| = _
    rw [brownianSquareStepProcess_cell _ T n p.2 i hi]
    change |reflectedFoldUnitSlope L (x + σ * B (brownianDyadicGrid T n i.castSucc) p.2)| =
      (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
    simpa only [Set.indicator_of_mem hp] using reflectedFoldUnitSlope_abs L hL _
  · change |brownianSquareStepProcess _ T n p| = _
    rw [brownianSquareStepProcess_outside _ T n p.2 hp]
    change |(0 : ℝ)| = (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
    simp only [Set.indicator_of_notMem hp, abs_zero]

theorem brownianFoldUnitTimeGrid_tendsto_ae (hB : IsBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianFoldUnitTimeGrid B L x σ T n p) atTop
        (𝓝 (brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p)) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hc : ∀ᵐ p ∂(volume : Measure ℝ).prod P, Continuous (fun t => B t p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := P)).ae hB.cont
  filter_upwards [hc, brownian_affine_ne_lattice_prod_ae hB.toIsPreBrownianReal hjoint L x hσ T]
    with p hpath hcorner
  have ht : Tendsto (fun n => brownianFoldUnitTimeGrid B L x σ T n p) atTop
      (𝓝 (brownianSquareProcess (fun t ω => reflectedFoldUnitSlope L (x + σ * B t ω)) T p)) := by
    apply brownianSquareStepProcess_tendsto_at
    intro hp
    have hinput : ContinuousAt (fun t : ℝ≥0 => x + σ * B t p.2) p.1.toNNReal :=
      (continuous_const.add (continuous_const.mul hpath)).continuousAt
    exact ContinuousAt.comp (f := fun t : ℝ≥0 => x + σ * B t p.2)
      (g := reflectedFoldUnitSlope L) (reflectedFoldUnitSlope_continuousAt L hL _ (hcorner hp)) hinput
  have he : brownianSquareProcess (fun t ω => reflectedFoldUnitSlope L (x + σ * B t ω)) T p =
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p := by
    change (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * reflectedFoldUnitSlope L (x + σ * B p.1.toNNReal p.2) =
      (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * reflectedFoldSlope L (x + σ * B p.1.toNNReal p.2)
    by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
    · rw [reflectedFoldUnitSlope_eq L hL _ (hcorner hp)]
    · simp only [Set.indicator_of_notMem hp, zero_mul]
  rwa [he] at ht

theorem brownianFoldUnitTimeGrid_error_le (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    (brownianFoldUnitTimeGrid B L x σ T n p -
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2 ≤
        4 * brownianIntervalIndicator 0 T p.1 := by
  have hA := (brownianFoldUnitTimeGrid_abs B L hL x σ T n p).le
  have hS := brownianBoundedProcess_abs_le B (fun z => reflectedFoldSlope_bound L hL (x + σ * z)) T p
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hi : brownianIntervalIndicator 0 T p.1 = 1 := Set.indicator_of_mem hp _
    rw [hi] at hA hS ⊢
    have he : |brownianFoldUnitTimeGrid B L x σ T n p -
        brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr he
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_one] using hs
  · have hi : brownianIntervalIndicator 0 T p.1 = 0 := Set.indicator_of_notMem hp _
    rw [hi] at hA hS ⊢
    have ha : brownianFoldUnitTimeGrid B L x σ T n p = 0 := abs_eq_zero.mp (le_antisymm hA (abs_nonneg _))
    have hs : brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa only [mul_zero] using hS) (abs_nonneg _))
    simp only [ha, hs, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]

theorem brownianFoldUnitTimeGrid_squared_error_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p, (brownianFoldUnitTimeGrid B L x σ T n p -
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2
        ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hh : Measurable (fun z => reflectedFoldSlope L (x + σ * z)) :=
    (reflectedFoldSlope_measurable L hL).comp (measurable_const.add (measurable_const.mul measurable_id))
  have hbInt : Integrable (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1) (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const (4 : ℝ) : Integrable (fun _ : Ω => (4 : ℝ)) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have hlim : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => (brownianFoldUnitTimeGrid B L x σ T n p -
        brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2) atTop (𝓝 0) := by
    filter_upwards [brownianFoldUnitTimeGrid_tendsto_ae hB hjoint L hL x hσ T] with p hp
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hp.sub_const (brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p)).pow 2
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianFoldUnitTimeGrid_measurable hBm L hL x σ T n).sub
      (brownianBoundedProcess_measurable hh hjoint T)).pow_const 2).aestronglyMeasurable) hbInt
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using
        brownianFoldUnitTimeGrid_error_le B L hL x σ T n p)) hlim
  simpa only [Pi.sub_apply, integral_zero] using hd

end TimeTraps.Probability
