module

public import TimeTraps.Probability.BrownianAdaptedContinuousProcess
public import TimeTraps.Probability.BrownianLocalTimeLevelNull

@[expose] public section

/-! Countably many scalar discontinuities are avoided at almost every
positive time/sample pair by the actual Gaussian one-time laws. Together
with Brownian path continuity this proves convergence of the actual left
dyadic samples. No continuity of the composed process at every time is
asserted, and the zero horizon is retained by the time cutoff. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {C : Set ℝ}

theorem brownian_eval_notMem_countable_ae (hB : IsPreBrownianReal B P)
    {t : ℝ≥0} (ht : 0 < t) (hC : C.Countable) :
    ∀ᵐ ω ∂P, B t ω ∉ C := by
  let : Countable C := hC.to_subtype
  have ha : ∀ᵐ ω ∂P, ∀ a : C, B t ω ≠ a.val :=
    ae_all_iff.mpr (fun a => brownian_eval_ne_level_ae hB ht a.val)
  filter_upwards [ha] with ω hω
  intro hm
  exact hω ⟨B t ω, hm⟩ rfl

theorem brownian_positive_time_notMem_countable_prod_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (hC : C.Countable) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      p.1 ∈ Ioc (0 : ℝ) T.val → B p.1.toNNReal p.2 ∉ C := by
  let : Countable C := hC.to_subtype
  have ha : ∀ᵐ p ∂(volume : Measure ℝ).prod P, ∀ a : C,
      p.1 ∈ Ioc (0 : ℝ) T.val → B p.1.toNNReal p.2 ≠ a.val :=
    ae_all_iff.mpr (fun a => brownian_positive_time_ne_level_prod_ae hB hjoint a.val T)
  filter_upwards [ha] with p hp ht
  intro hm
  exact hp ⟨B p.1.toNNReal p.2, hm⟩ ht rfl

theorem brownianCountable_continuousAt_prod_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (hC : C.Countable)
    (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      p.1 ∈ Ioc (0 : ℝ) T.val → ContinuousAt g (B p.1.toNNReal p.2) := by
  filter_upwards [brownian_positive_time_notMem_countable_prod_ae hB hjoint hC T] with p hp ht
  exact hc _ (hp ht)

theorem brownianCountable_step_tendsto_ae (hB : IsBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (hC : C.Countable)
    (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianSquareStepProcess (fun t ω => g (B t ω)) T n p) atTop
        (𝓝 (brownianBoundedProcess B g T p)) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hp : ∀ᵐ p ∂(volume : Measure ℝ).prod P, Continuous (fun t => B t p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := P)).ae hB.cont
  filter_upwards [hp, brownianCountable_continuousAt_prod_ae hB.toIsPreBrownianReal
    hjoint hC hc T] with p hpath hg
  apply brownianSquareStepProcess_tendsto_at
  intro ht
  exact ContinuousAt.comp (f := fun t : ℝ≥0 => B t p.2) (g := g)
    (hg ht) hpath.continuousAt

end TimeTraps.Probability
