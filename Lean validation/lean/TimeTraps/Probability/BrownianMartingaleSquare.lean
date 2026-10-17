module

public import TimeTraps.Probability.BrownianMartingaleFiltration
public import TimeTraps.Probability.BrownianMartingaleMoments

@[expose] public section

/-! The compensated square of the actual Brownian process is a martingale
in its raw natural filtration. This uses only conditional Gaussian moments
and the pull-out property; no stochastic-integral theorem is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_increment_square_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (B t ω - B s ω) ^ 2 | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun _ => t.val - s.val := by
  have h := brownian_increment_function_condExp hB hBm hst (fun x => x ^ 2) (by fun_prop)
  rw [brownian_increment_second_moment hB s t,
    abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst))] at h
  exact h

theorem brownian_increment_cross_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[B s * (B t - B s) | brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
  have hp := (hB.hasLaw_eval s).hasGaussianLaw.memLp_two.integrable_mul
    (brownian_increment_memLp hB s t 2 (by norm_num))
  have h := condExp_mul_of_stronglyMeasurable_left
    (brownianNaturalFiltration_stronglyAdapted B hBm s) hp
    ((hB.integrable_eval t).sub (hB.integrable_eval s))
  refine h.trans ?_
  filter_upwards [brownian_increment_condExp hB hBm hst] with ω hω
  simp only [Pi.mul_apply, hω, Pi.zero_apply, mul_zero]

theorem brownian_square_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => B t ω ^ 2 | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => B s ω ^ 2 + (t.val - s.val) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let u : Ω → ℝ := fun ω => B s ω ^ 2
  let v : Ω → ℝ := (2 : ℝ) • (B s * (B t - B s))
  let w : Ω → ℝ := fun ω => (B t ω - B s ω) ^ 2
  have hu : Integrable u P := brownian_eval_integrable_sq hB s
  have hp := (hB.hasLaw_eval s).hasGaussianLaw.memLp_two.integrable_mul
    (brownian_increment_memLp hB s t 2 (by norm_num))
  have hv : Integrable v P := hp.smul 2
  have hw : Integrable w P := brownian_increment_integrable_sq hB s t
  have h := (condExp_add (hu.add hv) hw (brownianNaturalFiltration B hBm s)).trans
    ((condExp_add hu hv (brownianNaturalFiltration B hBm s)).add Filter.EventuallyEq.rfl)
  have he : u + v + w = fun ω => B t ω ^ 2 := by
    funext ω
    dsimp [u, v, w]
    ring
  have hcu : P[u | brownianNaturalFiltration B hBm s] = u :=
    condExp_of_stronglyMeasurable ((brownianNaturalFiltration B hBm).le s)
      ((brownianNaturalFiltration_stronglyAdapted B hBm s).pow 2) hu
  rw [he, hcu] at h
  have hvs : P[v | brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
    have hscale := condExp_smul (μ := P) (2 : ℝ) (B s * (B t - B s))
      (brownianNaturalFiltration B hBm s)
    refine hscale.trans ?_
    filter_upwards [brownian_increment_cross_condExp hB hBm hst] with ω hω
    simp only [Pi.smul_apply, hω, Pi.zero_apply, smul_zero]
  refine h.trans ?_
  filter_upwards [hvs, brownian_increment_square_condExp hB hBm hst] with ω hvω hwω
  change u ω + P[v | brownianNaturalFiltration B hBm s] ω +
    P[w | brownianNaturalFiltration B hBm s] ω = _
  change P[w | brownianNaturalFiltration B hBm s] ω = t.val - s.val at hwω
  rw [hvω, hwω]
  simp [u]

theorem brownian_compensated_square_martingale_natural (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) :
    Martingale (fun t ω => B t ω ^ 2 - t.val) (brownianNaturalFiltration B hBm) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨fun t => ((brownianNaturalFiltration_stronglyAdapted B hBm t).pow 2).sub
    stronglyMeasurable_const, ?_⟩
  intro s t hst
  have h := condExp_sub (brownian_eval_integrable_sq hB t)
    (integrable_const t.val) (brownianNaturalFiltration B hBm s)
  rw [condExp_const ((brownianNaturalFiltration B hBm).le s) t.val] at h
  refine h.trans ?_
  filter_upwards [brownian_square_condExp hB hBm hst] with ω hω
  change P[fun ω => B t ω ^ 2 | brownianNaturalFiltration B hBm s] ω - t.val = _
  rw [hω]
  ring

theorem brownianDyadicPath_compensated_square_martingale :
    Martingale (fun t ω => brownianDyadicPath t ω ^ 2 - t.val)
      brownianFiltration brownianDyadicMeasure :=
  brownian_compensated_square_martingale_natural brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable

end TimeTraps.Probability
