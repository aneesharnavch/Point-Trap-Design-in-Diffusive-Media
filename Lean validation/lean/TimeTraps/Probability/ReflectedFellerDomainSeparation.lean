module

public import TimeTraps.Probability.ReflectedFellerDomainPairing

@[expose] public section

/-! Cosine pairings separate actual continuous functions. Positivity of
the ordinary Lebesgue integral and continuity include both endpoints. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis

theorem reflectedFellerPairing_self_eq_zero (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (hf : reflectedFellerPairing L hL f f = 0) : f = 0 := by
  rw [reflectedFellerPairing_apply, reflectedFellerMean_apply] at hf
  have he : (∫ x in 0..L, reflectedFellerExtension L hL (f * f) x) = 0 :=
    (mul_eq_zero.mp hf).resolve_left (inv_ne_zero hL.ne')
  rw [intervalIntegral.integral_of_le hL.le, ← integral_Icc_eq_integral_Ioc] at he
  have ha : reflectedFellerExtension L hL (f * f) =ᵐ[volume.restrict (Icc 0 L)] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => mul_self_nonneg (reflectedFellerExtension L hL f x))
      ((reflectedFellerExtension L hL (f * f)).continuous.integrableOn_Icc)).mp he
  have hz : reflectedFellerExtension L hL f =ᵐ[volume.restrict (Icc 0 L)] 0 := by
    filter_upwards [ha] with x hx
    exact eq_zero_of_mul_self_eq_zero hx
  have heq := Measure.eqOn_Icc_of_ae_eq volume hL.ne hz
    (reflectedFellerExtension L hL f).continuous.continuousOn continuousOn_const
  ext x
  rw [← reflectedFellerExtension_on_interval L hL f x]
  exact heq x.property

theorem reflectedFeller_cosine_pairings_separate_zero (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ))
    (hf : ∀ n : ℕ, reflectedFellerPairing L hL (neumannCosine L n) f = 0) : f = 0 := by
  let A := reflectedFellerPairing L hL f
  have hm : EqOn A.toLinearMap (0 : C(Icc (0 : ℝ) L, ℝ) →ₗ[ℝ] ℝ)
      (Set.range (fun n : ℕ => neumannCosine L n)) := by
    rintro _ ⟨n, rfl⟩
    exact (reflectedFellerPairing_comm L hL f (neumannCosine L n)).trans (hf n)
  have he : EqOn A (fun _ => (0 : ℝ)) (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) := by
    intro u hu
    change u ∈ neumannCosineSpan L at hu
    rw [neumannCosineSpan_eq_natSpan] at hu
    exact LinearMap.eqOn_span hm hu
  have hd : Dense (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, neumannCosineAlgebra_dense L hL]
    rfl
  exact reflectedFellerPairing_self_eq_zero L hL f
    (congrFun (Continuous.ext_on hd A.continuous continuous_const he) f)

theorem reflectedFeller_cosine_pairings_separate (L : ℝ) (hL : 0 < L)
    (f g : C(Icc (0 : ℝ) L, ℝ))
    (hfg : ∀ n : ℕ, reflectedFellerPairing L hL (neumannCosine L n) f =
      reflectedFellerPairing L hL (neumannCosine L n) g) : f = g := by
  apply sub_eq_zero.mp
  apply reflectedFeller_cosine_pairings_separate_zero L hL (f - g)
  intro n
  rw [map_sub, hfg n, sub_self]

end TimeTraps.Probability
