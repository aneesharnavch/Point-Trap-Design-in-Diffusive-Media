module

public import TimeTraps.Probability.BrownianIntegralTimeContinuityAmbient

@[expose] public section

/-! Continuous time maps in the completed integrand and output L² spaces,
and mean-square continuity of the raw-filtration martingale representative.
These conclusions concern L² topology, not continuity of sample paths. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianTimeCutoff_continuous (f : brownianIntegralSpace B hBm P) :
    Continuous (fun t => brownianTimeCutoff B hBm P t f) := by
  apply continuous_induced_rng.mpr
  exact brownianTimeCutoffAmbient_continuous P (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))

def brownianTimeCutoffContinuous (f : brownianIntegralSpace B hBm P) :
    C(ℝ≥0, brownianIntegralSpace B hBm P) :=
  ⟨fun t => brownianTimeCutoff B hBm P t f, brownianTimeCutoff_continuous f⟩

theorem brownianIntegralUpTo_continuous (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) : Continuous (fun t => brownianIntegralUpTo hB t f) :=
  (brownianIntegral hB).continuous.comp (brownianTimeCutoff_continuous f)

def brownianIntegralUpToContinuous (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) : C(ℝ≥0, Lp ℝ 2 P) :=
  ⟨fun t => brownianIntegralUpTo hB t f, brownianIntegralUpTo_continuous hB f⟩

def brownianIntegralProcessL2 (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) : Lp ℝ 2 P :=
  (brownianIntegralProcess_memLp hB f t).toLp (brownianIntegralProcess hB f t)

theorem brownianIntegralProcessL2_eq (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) :
    brownianIntegralProcessL2 hB f t = brownianIntegralUpTo hB t f := by
  apply Lp.ext
  exact ((brownianIntegralProcess_memLp hB f t).coeFn_toLp).trans
    (brownianIntegralProcess_ae hB f t)

theorem brownianIntegralProcessL2_continuous (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) : Continuous (brownianIntegralProcessL2 hB f) := by
  have he : brownianIntegralProcessL2 hB f = fun t => brownianIntegralUpTo hB t f :=
    funext (brownianIntegralProcessL2_eq hB f)
  rw [he]
  exact brownianIntegralUpTo_continuous hB f

theorem brownianIntegralProcess_increment_norm_sq (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s t : ℝ≥0) :
    (∫ ω, (brownianIntegralProcess hB f s ω - brownianIntegralProcess hB f t ω) ^ 2 ∂P) =
      ‖brownianIntegralUpTo hB s f - brownianIntegralUpTo hB t f‖ ^ 2 := by
  calc
    _ = ∫ ω, (brownianIntegral hB
        (brownianTimeCutoff B hBm P s f - brownianTimeCutoff B hBm P t f)) ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianIntegralProcess_increment_ae hB f t s] with ω hω
      rw [hω]
    _ = ‖brownianIntegral hB
        (brownianTimeCutoff B hBm P s f - brownianTimeCutoff B hBm P t f)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [Real.inner_apply, pow_two]
    _ = _ := by rw [map_sub]; rfl

theorem brownianIntegralProcess_meanSquare_tendsto (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) :
    Tendsto (fun s => ∫ ω,
      (brownianIntegralProcess hB f s ω - brownianIntegralProcess hB f t ω) ^ 2 ∂P)
      (𝓝 t) (𝓝 0) := by
  simp only [brownianIntegralProcess_increment_norm_sq]
  have hc : ContinuousAt (fun s =>
      ‖brownianIntegralUpTo hB s f - brownianIntegralUpTo hB t f‖ ^ 2) t :=
    (((brownianIntegralUpTo_continuous hB f).continuousAt.sub continuousAt_const).norm.pow 2)
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hc.tendsto

theorem brownianIntegralUpTo_zero_tendsto (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) :
    Tendsto (fun t => brownianIntegralUpTo hB t f) (𝓝 0) (𝓝 0) := by
  simpa only [brownianIntegralUpTo_zero] using
    ((brownianIntegralUpTo_continuous hB f).continuousAt (x := 0)).tendsto

theorem brownianIntegralProcess_meanSquare_zero_tendsto (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) :
    Tendsto (fun t => ∫ ω, brownianIntegralProcess hB f t ω ^ 2 ∂P) (𝓝 0) (𝓝 0) := by
  have he (t : ℝ≥0) : (∫ ω, brownianIntegralProcess hB f t ω ^ 2 ∂P) =
      ∫ ω, (brownianIntegralProcess hB f t ω - brownianIntegralProcess hB f 0 ω) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [brownianIntegralProcess_zero_ae hB f] with ω hω
    change brownianIntegralProcess hB f 0 ω = 0 at hω
    rw [hω, sub_zero]
  simpa only [he] using brownianIntegralProcess_meanSquare_tendsto hB f 0

theorem brownianStochasticIntegralProcess_meanSquare_tendsto (f : BrownianIntegrand) (t : ℝ≥0) :
    Tendsto (fun s => ∫ ω,
      (brownianStochasticIntegralProcess f s ω - brownianStochasticIntegralProcess f t ω) ^ 2
        ∂brownianDyadicMeasure) (𝓝 t) (𝓝 0) :=
  brownianIntegralProcess_meanSquare_tendsto brownianDyadicPath_isPreBrownianReal f t

end TimeTraps.Probability

end
