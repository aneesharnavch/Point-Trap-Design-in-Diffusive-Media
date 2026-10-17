module

public import TimeTraps.Probability.BrownianSignIntegrandConvergence

@[expose] public section

/-! The sign process belongs to the independently completed Brownian
integrand space because its bounded Lipschitz approximations converge
in product L². No density assertion for a larger process space is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSignProcessL2_mem (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T) ∈ brownianIntegralSpace B hBm P := by
  have hc : IsClosed (brownianIntegralSpace B hBm P : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure
  exact hc.mem_of_tendsto (brownianSignProcessL2_tendsto hB hjoint a T)
    (Eventually.of_forall (fun n => brownianLipschitzProcessL2_mem hB hBm
      (brownianSignApprox_lipschitz a n) hjoint T))

noncomputable def brownianSignIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  ⟨brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T),
    brownianSignProcessL2_mem hB hBm hjoint a T⟩

theorem brownianSignIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    (brownianSignIntegrand hB hBm hjoint a T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * Real.sign (B p.1.toNNReal p.2 - a)) :=
  brownianSignProcessL2_coe B a T (brownianSignProcess_memLp hB hjoint a T)

theorem brownianSignIntegrand_approximation_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => brownianLipschitzIntegrand hB hBm (brownianSignApprox_lipschitz a n) hjoint T)
      atTop (𝓝 (brownianSignIntegrand hB hBm hjoint a T)) :=
  tendsto_subtype_rng.mpr (brownianSignProcessL2_tendsto hB hjoint a T)

theorem brownianSignIntegrand_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) :
    brownianSignIntegrand hB hBm hjoint a 0 = 0 := by
  apply Subtype.ext
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [brownianSignIntegrand_coe hB hBm hjoint a 0] with p hp
  rw [hp]
  simp

noncomputable def brownianDyadicSignIntegrand (a : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  brownianSignIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T

theorem brownianDyadicSignIntegrand_coe (a : ℝ) (T : ℝ≥0) :
    (brownianDyadicSignIntegrand a T : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))
      =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        Real.sign (brownianDyadicPath p.1.toNNReal p.2 - a)) :=
  brownianSignIntegrand_coe brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T

end TimeTraps.Probability
