module

public import TimeTraps.Probability.ReflectedContinuousDynkinConditional
public import TimeTraps.Probability.ReflectedNeumannDynkinVariation
public import TimeTraps.Probability.ReflectedNeumannDynkinProcess
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The full C² Neumann Dynkin conditional law for the actual folded
trajectory, and raw-filtration martingale representatives. The ordinary
time integral of the continuous curvature is the compensator. Each fixed
time representative equals the literal expression almost surely; no
filtration completion or uncountable intersection of null events is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

set_option maxHeartbeats 1000000 in
theorem reflectedNeumannDynkin_condExp {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (D : ℝ) (hD : 0 < D) (x : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[reflectedNeumannDynkin F hL B D x t | brownianNaturalFiltration B hBm s] =ᵐ[P]
      reflectedNeumannDynkin F hL B D x s := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let C (r : ℝ≥0) : Ω → ℝ := fun ω => reflectedContinuousInput L hL D x F.valueMap (B r ω)
  let A (r : ℝ≥0) := brownianItoDrift B (reflectedContinuousInput L hL D x F.curvatureMap) r
  let m := brownianNaturalFiltration B hBm s
  let I (ω : Ω) : ℝ := ∫ r in s.val..t.val, reflectedContinuousInput L hL D x
    (reflectedFellerTimeOperator L hL D (r - s.val) F.curvatureMap) (B s ω)
  let R (ω : Ω) := reflectedContinuousInput L hL D x
    (reflectedFellerTimeOperator L hL D (t.val - s.val) F.valueMap) (B s ω)
  have hCi (r : ℝ≥0) : Integrable (C r) P :=
    (reflectedContinuousInput_eval_memLp hBm L hL D x F.valueMap r).integrable (by norm_num)
  have hg := reflectedContinuousInput_continuous L hL D x F.curvatureMap
  have hb := reflectedContinuousInput_bound L hL D x F.curvatureMap
  have hAi (r : ℝ≥0) : Integrable (A r) P :=
    (brownianItoDrift_bounded_memLp hg.measurable hjoint hb r).integrable (by norm_num)
  have h0m : StronglyMeasurable[m] (C 0) :=
    (reflectedContinuousInput_continuous L hL D x F.valueMap).comp_stronglyMeasurable
      ((brownianNaturalFiltration_stronglyAdapted B hBm 0).mono
        ((brownianNaturalFiltration B hBm).mono (show (0 : ℝ≥0) ≤ s from zero_le)))
  have h0 : P[C 0 | m] =ᵐ[P] C 0 := condExp_of_aestronglyMeasurable'
    ((brownianNaturalFiltration B hBm).le s) h0m.aestronglyMeasurable (hCi 0)
  have hl : P[C t - C 0 - D • A t | m] =ᵐ[P]
      P[C t | m] - P[C 0 | m] - D • P[A t | m] :=
    (condExp_sub ((hCi t).sub (hCi 0)) ((hAi t).smul D) m).trans
      ((condExp_sub (hCi t) (hCi 0) m).sub (condExp_smul D (A t) m))
  have hs := condExp_sub (hAi t) (hAi s) m
  have hd := reflectedContinuous_drift_increment_condExp hB.toIsPreBrownianReal hBm hjoint
    L hL D hD x F.curvatureMap hst
  have hp := brownianItoDrift_continuous_condExp_past hB hBm hg hb hjoint (le_refl s)
  have ht := reflectedContinuousInput_condExp hB.toIsPreBrownianReal hBm
    L hL D hD x F.valueMap hst
  have hv (ω : Ω) : R ω - C s ω = D * I ω :=
    F.feller_integral_apply_shift hL D hD.le (show s.val ≤ t.val from hst)
      (reflectedIntervalFold L hL (x + Real.sqrt (2 * D) * B s ω))
  filter_upwards [hl, hs, hd, hp, ht, h0] with ω hlω hsω hdω hpω htω h0ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hlω hsω
  have hA : P[A t | m] ω = A s ω + I ω := by
    change P[A t - A s | m] ω = I ω at hdω
    change P[A s | m] ω = A s ω at hpω
    rw [hsω, hpω] at hdω
    linarith
  change P[C t - C 0 - D • A t | m] ω = C s ω - C 0 ω - D * A s ω
  rw [hlω, htω, h0ω, hA]
  change R ω - C 0 ω - D * (A s ω + I ω) = C s ω - C 0 ω - D * A s ω
  nlinarith [hv ω]

noncomputable def reflectedNeumannDynkinVersion {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) (P : Measure Ω)
    (D x : ℝ) (t : ℝ≥0) : Ω → ℝ :=
  P[reflectedNeumannDynkin F hL B D x t | brownianNaturalFiltration B hBm t]

theorem reflectedNeumannDynkinVersion_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (D x : ℝ) (t : ℝ≥0) :
    reflectedNeumannDynkinVersion F hL B hBm P D x t =ᵐ[P]
      reflectedNeumannDynkin F hL B D x t := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  exact condExp_of_aestronglyMeasurable' ((brownianNaturalFiltration B hBm).le t)
    (reflectedNeumannDynkin_aestronglyMeasurable F hL hB hBm D x t)
    ((reflectedNeumannDynkin_memLp F hL hBm hjoint D x t).integrable (by norm_num))

theorem reflectedNeumannDynkinVersion_martingale {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (D : ℝ) (hD : 0 < D) (x : ℝ) :
    Martingale (reflectedNeumannDynkinVersion F hL B hBm P D x)
      (brownianNaturalFiltration B hBm) P := by
  refine ⟨fun _ => stronglyMeasurable_condExp, fun s t hst => ?_⟩
  exact (condExp_congr_ae (reflectedNeumannDynkinVersion_ae F hL hB hBm hjoint D x t)).trans
    ((reflectedNeumannDynkin_condExp F hL hB hBm hjoint D hD x hst).trans
      (reflectedNeumannDynkinVersion_ae F hL hB hBm hjoint D x s).symm)

theorem reflectedNeumannDynkinVersion_physical_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (D x : ℝ) (t : ℝ≥0) :
    reflectedNeumannDynkinVersion F hL B hBm P D x t =ᵐ[P] (fun ω =>
      F.value (foldedTrajectory L D x B t ω) - F.value (foldedTrajectory L D x B 0 ω) -
        D * ∫ r in (0 : ℝ)..t.val, F.curvature (foldedTrajectory L D x B r.toNNReal ω)) :=
  (reflectedNeumannDynkinVersion_ae F hL hB hBm hjoint D x t).trans
    (Eventually.of_forall (reflectedNeumannDynkin_physical F hL B D x t))

theorem brownianDyadic_reflectedNeumann_dynkin_martingale {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) :
    Martingale (reflectedNeumannDynkinVersion F hL brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure D x) brownianFiltration brownianDyadicMeasure :=
  reflectedNeumannDynkinVersion_martingale F hL brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable D hD x

end TimeTraps.Probability
