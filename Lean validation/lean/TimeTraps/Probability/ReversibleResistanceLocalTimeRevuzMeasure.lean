module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuz

@[expose] public section

/-! The unnormalized physical speed measure rho(x) dx and the literal
Revuz identity written as an expectation from that measure. It is finite,
and the contact test has the atom delta_a without a mass-normalization
factor. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def reversibleResistanceSpeedMeasure (A : IntervalMedium) :
    Measure (Icc A.source.left A.source.right) :=
  (reversibleResistanceLengthMeasure A).withDensity (fun x => ENNReal.ofReal (A.source.density x.val))

instance reversibleResistanceSpeedMeasure_finite (A : IntervalMedium) :
    IsFiniteMeasure (reversibleResistanceSpeedMeasure A) := by
  let w : C(Icc A.source.left A.source.right, ℝ) :=
    ⟨fun x => A.source.density x.val,
      A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)⟩
  have hi : Integrable w (reversibleResistanceLengthMeasure A) :=
    w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x : Icc A.source.left A.source.right =>
      (A.source.positive x.val x.property).le))).mp hi.hasFiniteIntegral).ne

theorem reversibleResistanceSpeedMeasure_integral (A : IntervalMedium)
    (H : Icc A.source.left A.source.right → ℝ) :
    (∫ x, H x ∂reversibleResistanceSpeedMeasure A) =
      ∫ x, A.source.density x.val * H x ∂reversibleResistanceLengthMeasure A := by
  have hm : Measurable (fun x : Icc A.source.left A.source.right => ENNReal.ofReal (A.source.density x.val)) :=
    (A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)).measurable.ennreal_ofReal
  rw [reversibleResistanceSpeedMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [ENNReal.toReal_ofReal (A.source.positive x.val x.property).le, smul_eq_mul]

theorem reversibleResistanceSpeedMeasure_integral_interval (A : IntervalMedium) (H : ℝ → ℝ) :
    (∫ x, H x.val ∂reversibleResistanceSpeedMeasure A) =
      ∫ x in A.source.left..A.source.right, A.source.density x * H x :=
  (reversibleResistanceSpeedMeasure_integral A (fun x => H x.val)).trans
    (reversibleResistanceLengthMeasure_integral A (fun x => A.source.density x * H x))

theorem reversibleResistanceSpeedMeasure_integrable_iff (A : IntervalMedium)
    (H : Icc A.source.left A.source.right → ℝ) :
    Integrable H (reversibleResistanceSpeedMeasure A) ↔
      Integrable (fun x => A.source.density x.val * H x) (reversibleResistanceLengthMeasure A) := by
  have hm : Measurable (fun x : Icc A.source.left A.source.right => ENNReal.ofReal (A.source.density x.val)) :=
    (A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)).measurable.ennreal_ofReal
  rw [reversibleResistanceSpeedMeasure, integrable_withDensity_iff_integrable_smul' hm
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun x : Icc A.source.left A.source.right =>
      (ENNReal.ofReal (A.source.density x.val)).toReal • H x) =
      (fun x => A.source.density x.val * H x) := by
    funext x
    rw [ENNReal.toReal_ofReal (A.source.positive x.val x.property).le, smul_eq_mul]
  rw [he]

theorem reversibleResistanceRevuzContact_speed_integrable (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) (T : ℝ≥0) :
    Integrable (fun x => f x.val *
      (∫ ω, reversibleResistanceRevuzContact A x.val a.val g T ω ∂brownianDyadicMeasure))
        (reversibleResistanceSpeedMeasure A) := by
  apply (reversibleResistanceSpeedMeasure_integrable_iff A _).mpr
  have hi := (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
    (reversibleResistanceRevuzMeanTest_integrable A a hf g T)
  apply hi.congr
  apply Eventually.of_forall
  intro x
  change A.source.density x.val * f x.val * _ = A.source.density x.val * (f x.val * _)
  ring

theorem reversibleResistanceRevuzContact_speed_identity (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ x, f x.val * (∫ ω, reversibleResistanceRevuzContact A x.val a.val g T ω ∂brownianDyadicMeasure)
      ∂reversibleResistanceSpeedMeasure A) =
      g a.val * ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f a.val := by
  calc
    _ = ∫ x in A.source.left..A.source.right, A.source.density x *
        (f x * (∫ ω, reversibleResistanceRevuzContact A x a.val g T ω ∂brownianDyadicMeasure)) :=
      reversibleResistanceSpeedMeasure_integral_interval A _
    _ = ∫ x in A.source.left..A.source.right, reversibleResistanceRevuzMeanTest A a.val f g T x := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold reversibleResistanceRevuzMeanTest
      ring
    _ = _ := reversibleResistanceRevuzMeanTest_spatial_identity A a hf g T

theorem reversibleResistanceRevuz_limit_speedMeasure (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x, f x.val *
      (∫ ω, reversibleResistanceRevuzContact A x.val a.val g t.toNNReal ω ∂brownianDyadicMeasure)
        ∂reversibleResistanceSpeedMeasure A) (𝓝[>] 0) (𝓝 (f a.val * g a.val)) := by
  apply (reversibleResistanceRevuz_limit_speed A a hf g).congr
  intro t
  congr 1
  exact (reversibleResistanceRevuzMeanTest_spatial_identity A a hf g t.toNNReal).trans
    (reversibleResistanceRevuzContact_speed_identity A a hf g t.toNNReal).symm

end TimeTraps.Probability
