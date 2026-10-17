module

public import TimeTraps.Probability.BrownianFoldSlopeUnit
public import TimeTraps.Probability.BrownianIntegralSquareGrid
public import TimeTraps.Probability.BrownianBoundedIntegrandProcess

@[expose] public section

/-! Actual finite left-time-grid samples of the fold slope. Continuity
of Brownian paths and exclusion of the corner lattice give product-almost-
everywhere convergence, including the zero process at a zero horizon. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianDyadicGrid_left_tendsto (T : ℝ≥0) {r : ℝ} (hr : r ∈ Ioc 0 T.val)
    (i : (n : ℕ) → Fin (2 ^ n))
    (hi : ∀ n, r ∈ Ioc (brownianDyadicGrid T n (i n).castSucc).val
      (brownianDyadicGrid T n (i n).succ).val) :
    Tendsto (fun n => brownianDyadicGrid T n (i n).castSucc) atTop (𝓝 r.toNNReal) := by
  have hb (n : ℕ) : dist (brownianDyadicGrid T n (i n).castSucc) r.toNNReal ≤ T.val / (2 : ℝ) ^ n := by
    calc
      _ = |(brownianDyadicGrid T n (i n).castSucc).val - r| :=
        congrArg (fun a : ℝ => |(brownianDyadicGrid T n (i n).castSucc).val - a|)
          (Real.coe_toNNReal r hr.1.le)
      _ ≤ _ := by
        rw [abs_of_nonpos (sub_nonpos.mpr (hi n).1.le)]
        have hg := brownianDyadicGrid_gap T n (i n)
        have hgrid : (brownianDyadicGrid T n (i n).castSucc).val ≤
            (brownianDyadicGrid T n (i n).succ).val :=
          brownianDyadicGrid_monotone T n (show (i n).castSucc ≤ (i n).succ by exact Nat.le_succ _)
        rw [abs_of_nonneg (sub_nonneg.mpr hgrid)] at hg
        linarith [(hi n).2]
  have hm : Tendsto (fun n => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hb hm)

theorem brownianSquareStepProcess_tendsto_at (C : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (p : ℝ × Ω) (hc : p.1 ∈ Ioc (0 : ℝ) T.val → ContinuousAt (fun t => C t p.2) p.1.toNNReal) :
    Tendsto (fun n => brownianSquareStepProcess C T n p) atTop (𝓝 (brownianSquareProcess C T p)) := by
  classical
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · choose i hi using fun n => brownianDyadicGrid_cell T n hp
    have ht := (hc hp).tendsto.comp (brownianDyadicGrid_left_tendsto T hp i hi)
    have he (n : ℕ) : brownianSquareStepProcess C T n p = C (brownianDyadicGrid T n (i n).castSucc) p.2 :=
      brownianSquareStepProcess_cell C T n p.2 (i n) (hi n)
    simpa only [he, brownianSquareProcess, Set.indicator_of_mem hp, one_mul, Function.comp_def] using ht
  · have he (n : ℕ) : brownianSquareStepProcess C T n p = 0 :=
      brownianSquareStepProcess_outside C T n p.2 hp
    simpa only [he, brownianSquareProcess, Set.indicator_of_notMem hp, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

def brownianFoldSlopeTimeGrid (B : ℝ≥0 → Ω → ℝ) (L x σ : ℝ) (T : ℝ≥0) (n : ℕ) : ℝ × Ω → ℝ :=
  brownianSquareStepProcess (fun t ω => reflectedFoldSlope L (x + σ * B t ω)) T n

theorem brownianFoldSlopeTimeGrid_measurable (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) :
    Measurable (brownianFoldSlopeTimeGrid B L x σ T n) := by
  unfold brownianFoldSlopeTimeGrid brownianSquareStepProcess
  apply Finset.measurable_sum
  intro i _
  exact brownianElementaryProcess_measurable _ _ ((reflectedFoldSlope_measurable L hL).comp
    (measurable_const.add (measurable_const.mul (hBm _))))

theorem brownianFoldSlopeTimeGrid_abs_le (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    |brownianFoldSlopeTimeGrid B L x σ T n p| ≤ brownianIntervalIndicator 0 T p.1 := by
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hp
    change |brownianSquareStepProcess _ T n p| ≤ _
    rw [brownianSquareStepProcess_cell _ T n p.2 i hi]
    change |reflectedFoldSlope L (x + σ * B (brownianDyadicGrid T n i.castSucc) p.2)| ≤
      (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
    simpa only [Set.indicator_of_mem hp] using
      reflectedFoldSlope_bound L hL (x + σ * B (brownianDyadicGrid T n i.castSucc) p.2)
  · change |brownianSquareStepProcess _ T n p| ≤ _
    rw [brownianSquareStepProcess_outside _ T n p.2 hp]
    change |(0 : ℝ)| ≤ (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
    simp only [Set.indicator_of_notMem hp, abs_zero, le_refl]

theorem brownianFoldSlopeTimeGrid_memLp [IsFiniteMeasure P] (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) :
    MemLp (brownianFoldSlopeTimeGrid B L x σ T n) 2 ((volume : Measure ℝ).prod P) := by
  apply (brownianElementaryProcess_memLp (P := P) 0 T measurable_const (memLp_const (1 : ℝ))).mono'
    (brownianFoldSlopeTimeGrid_measurable hBm L hL x σ T n).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [brownianElementaryProcess, mul_one, Real.norm_eq_abs] using
    brownianFoldSlopeTimeGrid_abs_le B L hL x σ T n p

theorem brownianFoldSlopeTimeGrid_tendsto_ae (hB : IsBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianFoldSlopeTimeGrid B L x σ T n p) atTop
        (𝓝 (brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p)) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hc : ∀ᵐ p ∂(volume : Measure ℝ).prod P, Continuous (fun t => B t p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := P)).ae hB.cont
  filter_upwards [hc, brownianFoldSlope_continuousAt_prod_ae hB.toIsPreBrownianReal hjoint L hL x hσ T]
    with p hpath hslope
  apply brownianSquareStepProcess_tendsto_at
  intro ht
  have hinput : ContinuousAt (fun t : ℝ≥0 => x + σ * B t p.2) p.1.toNNReal :=
    (continuous_const.add (continuous_const.mul hpath)).continuousAt
  exact ContinuousAt.comp (f := fun t : ℝ≥0 => x + σ * B t p.2)
    (g := reflectedFoldSlope L) (hslope ht) hinput

end TimeTraps.Probability

end
