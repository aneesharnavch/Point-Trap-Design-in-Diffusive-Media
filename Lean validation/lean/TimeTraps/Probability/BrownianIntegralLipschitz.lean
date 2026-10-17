module

public import TimeTraps.Probability.BrownianIntegralLipschitzApproximation

@[expose] public section

/-! Every globally Lipschitz g(B_s), cut off to a finite horizon,
belongs to the actual completed Brownian integrand space. Membership is
proved by the left dyadic elementary approximation, with its explicit
L² rate. No density in a larger predictable space or Itô formula is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianLipschitzProcessL2_mem (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianLipschitzProcessL2 hB hg hjoint T ∈ brownianIntegralSpace B hBm P := by
  have hc : IsClosed (brownianIntegralSpace B hBm P : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure
  exact hc.mem_of_tendsto (brownianLipschitzStep_process_tendsto hB hBm hg hjoint T)
    (Eventually.of_forall (fun n => (brownianLipschitzStepIntegrand hB hBm hg T n).property))

noncomputable def brownianLipschitzIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  ⟨brownianLipschitzProcessL2 hB hg hjoint T, brownianLipschitzProcessL2_mem hB hBm hg hjoint T⟩

theorem brownianLipschitzIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (brownianLipschitzIntegrand hB hBm hg hjoint T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianLipschitzProcess B g T :=
  brownianLipschitzProcessL2_coe hB hg hjoint T

theorem brownianLipschitzIntegrand_step_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Tendsto (brownianLipschitzStepIntegrand hB hBm hg T) atTop
      (𝓝 (brownianLipschitzIntegrand hB hBm hg hjoint T)) :=
  tendsto_subtype_rng.mpr (brownianLipschitzStep_process_tendsto hB hBm hg hjoint T)

theorem brownianLipschitzIntegrand_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    brownianLipschitzIntegrand hB hBm hg hjoint 0 = 0 := by
  apply Subtype.ext
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [brownianLipschitzIntegrand_coe hB hBm hg hjoint 0] with p hp
  rw [hp]
  simp [brownianLipschitzProcess, brownianSquareProcess]

noncomputable def brownianDyadicLipschitzIntegrand (hg : LipschitzWith K g) (T : ℝ≥0) : BrownianIntegrand :=
  brownianLipschitzIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable hg
    brownianDyadicPath_jointly_measurable T

theorem brownianDyadicLipschitzIntegrand_coe (hg : LipschitzWith K g) (T : ℝ≥0) :
    (brownianDyadicLipschitzIntegrand hg T : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))
      =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        g (brownianDyadicPath p.1.toNNReal p.2)) :=
  brownianLipschitzIntegrand_coe brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable hg
    brownianDyadicPath_jointly_measurable T

theorem brownianDyadicLipschitzIntegrand_approximation_bound (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) :
    ‖(brownianLipschitzStepIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable hg T n :
        Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) -
      (brownianDyadicLipschitzIntegrand hg T : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))‖ ^ 2 ≤
        K.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n :=
  brownianLipschitzStep_process_error_le brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable hg
    brownianDyadicPath_jointly_measurable T n

end TimeTraps.Probability
