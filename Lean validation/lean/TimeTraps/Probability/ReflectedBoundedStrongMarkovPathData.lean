module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovBorel
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovCylinder
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Genuine Borel finite-horizon future paths. Measurability follows from
an injective dense evaluation map on the Polish continuous-path space,
not from assuming a law for random paths. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal

abbrev ReflectedMarkovPath (L : ℝ) (H : ℝ≥0) :=
  C(Icc (0 : ℝ≥0) H, Icc (0 : ℝ) L)

instance reflectedMarkovPathMeasurableSpace (L : ℝ) (H : ℝ≥0) :
    MeasurableSpace (ReflectedMarkovPath L H) := borel _

instance reflectedMarkovPathBorelSpace (L : ℝ) (H : ℝ≥0) :
    BorelSpace (ReflectedMarkovPath L H) := ⟨rfl⟩

def reflectedMarkovPathSample (L : ℝ) (H : ℝ≥0) (p : ReflectedMarkovPath L H) :
    ℕ → Icc (0 : ℝ) L := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, le_rfl, bot_le⟩⟩
  exact fun n => p (denseSeq (Icc (0 : ℝ≥0) H) n)

theorem reflectedMarkovPathSample_measurableEmbedding (L : ℝ) (H : ℝ≥0) :
    MeasurableEmbedding (reflectedMarkovPathSample L H) := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, le_rfl, bot_le⟩⟩
  have hc : Continuous (reflectedMarkovPathSample L H) :=
    continuous_pi (fun _ => continuous_eval_const _)
  apply hc.measurableEmbedding
  intro p q hpq
  apply ContinuousMap.coe_injective
  exact (denseRange_denseSeq (Icc (0 : ℝ≥0) H)).equalizer p.continuous q.continuous hpq

theorem reflectedMarkovPath_measurable_of_eval (L : ℝ) (H : ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (p : Ω → ReflectedMarkovPath L H)
    (hp : ∀ t, Measurable (fun ω => p ω t)) : Measurable p := by
  apply (reflectedMarkovPathSample_measurableEmbedding L H).measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n => hp _)

def reflectedMarkovFuturePath (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (τ : BrownianCompletedSample → ℝ≥0) (ω : BrownianCompletedSample) :
    ReflectedMarkovPath L H :=
  ⟨fun t => reflectedMarkovState L hL D x (τ ω + t.val) ω,
    (reflectedMarkovState_continuous L hL D x ω).comp
      (continuous_const.add continuous_subtype_val)⟩

theorem reflectedMarkovFuturePath_measurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (reflectedMarkovFuturePath L hL D x H τ) := by
  apply reflectedMarkovPath_measurable_of_eval
  intro t
  exact ((reflectedMarkovState_stopped_stronglyMeasurable L hL D x
    (reflectedMarkovStoppingTime_add hτ t.val)).mono
      (reflectedMarkovStoppingTime_add hτ t.val).measurableSpace_le).measurable

def reflectedMarkovFreshPath (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    (q : Icc (0 : ℝ) L × BrownianCompletedSample) : ReflectedMarkovPath L H :=
  reflectedMarkovFuturePath L hL D q.1.val H (fun _ => 0) q.2

theorem reflectedMarkovFreshPath_measurable (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0) :
    Measurable (reflectedMarkovFreshPath L hL D H) := by
  apply reflectedMarkovPath_measurable_of_eval
  intro t
  have hw : Measurable (fun q : Icc (0 : ℝ) L × BrownianCompletedSample =>
      reflectedMarkovBrownianPath t.val q.2) :=
    ((reflectedMarkovBrownianPath_stronglyAdapted t.val).mono
      (brownianCompletedFiltration.le t.val)).measurable.comp measurable_snd
  have hy : Measurable (fun q : Icc (0 : ℝ) L × BrownianCompletedSample => q.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hf := (reflectedIntervalFold L hL).continuous.measurable.comp
    (hy.add (hw.const_mul (Real.sqrt (2 * D))))
  simpa only [reflectedMarkovFreshPath, reflectedMarkovFuturePath,
    reflectedMarkovState, ContinuousMap.coe_mk, zero_add, Function.comp_def, Pi.add_apply] using hf

def reflectedMarkovContinuationPath (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (τ : BrownianCompletedSample → ℝ≥0)
    (q : BrownianCompletedSample × BrownianCompletedSample) : ReflectedMarkovPath L H :=
  reflectedMarkovFreshPath L hL D H (reflectedMarkovState L hL D x (τ q.1) q.1, q.2)

theorem reflectedMarkovContinuationPath_measurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (reflectedMarkovContinuationPath L hL D x H τ) :=
  (reflectedMarkovFreshPath_measurable L hL D H).comp
    ((((reflectedMarkovState_stopped_stronglyMeasurable L hL D x hτ).mono
      hτ.measurableSpace_le).measurable.comp measurable_fst).prodMk measurable_snd)

theorem reflectedMarkovFuturePath_actual_ae
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (τ : BrownianCompletedSample → ℝ≥0) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t : Icc (0 : ℝ≥0) H,
      (reflectedMarkovFuturePath L hL D x H τ ω t).val =
        foldedTrajectory L D x brownianDyadicPath (τ ω + t.val) ω := by
  filter_upwards [reflectedMarkovState_actual_ae L hL D x] with ω hω
  exact fun t => hω _

end TimeTraps.Probability

end
