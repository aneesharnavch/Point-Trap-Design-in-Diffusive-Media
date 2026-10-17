module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzIdentity
public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzContact
public import TimeTraps.Analysis.ReflectedAtomicRevuzAverage

@[expose] public section

/-! Literal physical Revuz test normalization relative to rho(x) dx.
For every continuous initial test and every spatial contact test, the
actual contact measure has atom delta_a. Both expectations and spatial
integrals are genuinely integrable; no symmetry or normalization premise
is added. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def reversibleResistanceRevuzMeanTest (A : IntervalMedium) (a : ℝ)
    (f g : ℝ → ℝ) (T : ℝ≥0) (x : ℝ) : ℝ :=
  A.source.density x * f x *
    ∫ ω, reversibleResistanceRevuzContact A x a g T ω ∂brownianDyadicMeasure

theorem reversibleResistanceRevuzMeanTest_integrable (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (reversibleResistanceRevuzMeanTest A a.val f g T)
      (Icc A.source.left A.source.right) volume := by
  apply ((reversibleResistanceLocalTime_speed_interval_integrable A a T hf).const_mul (g a.val)).congr
  apply Eventually.of_forall
  intro x
  unfold reversibleResistanceRevuzMeanTest
  rw [reversibleResistanceRevuzContact_mean A x a.property g T]
  ring

theorem reversibleResistanceRevuzMeanTest_spatial_identity (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ x in A.source.left..A.source.right, reversibleResistanceRevuzMeanTest A a.val f g T x) =
      g a.val * ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f a.val := by
  calc
    _ = ∫ x in A.source.left..A.source.right, g a.val * (A.source.density x * f x *
        (∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure)) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold reversibleResistanceRevuzMeanTest
      rw [reversibleResistanceRevuzContact_mean A x a.property g T]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, reversibleResistanceLocalTime_speed_interval A a T hf]

theorem reversibleResistanceRevuz_limit_speed (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x in A.source.left..A.source.right,
      reversibleResistanceRevuzMeanTest A a.val f g t.toNNReal x)
        (𝓝[>] 0) (𝓝 (f a.val * g a.val)) := by
  let F : ℝ → ℝ := fun s => reversibleResistanceTransition A s.toNNReal f a.val
  have hF : Continuous F :=
    (reversibleResistanceTransition_continuous_time A (Ioo_subset_Icc_self a.property) hf).comp
      continuous_real_toNNReal
  have hz : F 0 = f a.val := by
    dsimp only [F]
    rw [Real.toNNReal_zero]
    exact reversibleResistanceTransition_zero A f (Ioo_subset_Icc_self a.property)
  have ht := (reflectedAtomicRevuz_continuous_average hF).const_mul (g a.val)
  rw [hz, mul_comm (g a.val) (f a.val)] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hT : t.toNNReal.val = t := Real.coe_toNNReal t (le_of_lt ht)
  have htime : (∫ s in (0 : ℝ)..t.toNNReal.val, F s) = ∫ s in (0 : ℝ)..t, F s :=
    congrArg (fun q : ℝ => ∫ s in (0 : ℝ)..q, F s) hT
  have hs := reversibleResistanceRevuzMeanTest_spatial_identity A a hf g t.toNNReal
  change (∫ x in A.source.left..A.source.right, reversibleResistanceRevuzMeanTest A a.val f g t.toNNReal x) =
    g a.val * ∫ s in (0 : ℝ)..t.toNNReal.val, F s at hs
  calc
    g a.val * (t⁻¹ * ∫ s in (0 : ℝ)..t, F s) =
        t⁻¹ * (g a.val * ∫ s in (0 : ℝ)..t, F s) := by ring
    _ = t⁻¹ * (g a.val * ∫ s in (0 : ℝ)..t.toNNReal.val, F s) :=
      congrArg (fun v : ℝ => t⁻¹ * (g a.val * v)) htime.symm
    _ = _ := congrArg (fun v : ℝ => t⁻¹ * v) hs.symm

theorem reversibleResistanceRevuz_localTime_mass (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    (∫ x in A.source.left..A.source.right, A.source.density x *
      (∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure)) = T.val := by
  have he := reversibleResistanceLocalTime_speed_interval A a T (f := fun _ => (1 : ℝ)) continuousOn_const
  simpa only [mul_one, reversibleResistanceTransition_one, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] using he

end TimeTraps.Probability
