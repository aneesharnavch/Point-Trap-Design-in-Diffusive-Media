module

public import TimeTraps.Probability.ReflectedFellerCosineCore
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! The actual physical-time semigroup integral is a bounded linear map
on continuous functions. Its fundamental theorem gives a right generator
derivative from the variation identity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedFellerTimeOperator (L : ℝ) (hL : 0 < L) (D t : ℝ) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) :=
  reflectedFellerOperator L hL (Real.toNNReal (2 * D * t))

theorem reflectedFellerTimeOperator_continuous (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) : Continuous (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) :=
  (reflectedFellerOperator_continuous L hL f).comp (by fun_prop)

theorem reflectedFellerTimeIntegral_norm (L : ℝ) (hL : 0 < L) (D t : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    ‖∫ s in 0..t, reflectedFellerTimeOperator L hL D s f‖ ≤ |t| * ‖f‖ := by
  simpa only [reflectedFellerTimeOperator, sub_zero, mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (fun s _ => reflectedFellerOperator_contraction L hL
      (Real.toNNReal (2 * D * s)) f)

def reflectedFellerIntegralLinear (L : ℝ) (hL : 0 < L) (D t : ℝ) :
    C(Icc (0 : ℝ) L, ℝ) →ₗ[ℝ] C(Icc (0 : ℝ) L, ℝ) where
  toFun f := ∫ s in 0..t, reflectedFellerTimeOperator L hL D s f
  map_add' f g := by
    simp only [map_add]
    exact intervalIntegral.integral_add
      ((reflectedFellerTimeOperator_continuous L hL D f).intervalIntegrable 0 t)
      ((reflectedFellerTimeOperator_continuous L hL D g).intervalIntegrable 0 t)
  map_smul' c f := by
    simp only [map_smul]
    exact intervalIntegral.integral_smul c _

def reflectedFellerIntegralOperator (L : ℝ) (hL : 0 < L) (D t : ℝ) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) :=
  (reflectedFellerIntegralLinear L hL D t).mkContinuous |t| (fun f => by
    change ‖∫ s in 0..t, reflectedFellerTimeOperator L hL D s f‖ ≤ |t| * ‖f‖
    exact reflectedFellerTimeIntegral_norm L hL D t f)

theorem reflectedFellerIntegralOperator_apply (L : ℝ) (hL : 0 < L) (D t : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerIntegralOperator L hL D t f =
      ∫ s in 0..t, reflectedFellerTimeOperator L hL D s f := rfl

theorem reflectedFeller_generator_of_integral (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f g : C(Icc (0 : ℝ) L, ℝ))
    (h : ∀ t : ℝ, 0 ≤ t → reflectedFellerTimeOperator L hL D t f - f =
      reflectedFellerIntegralOperator L hL D t g) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0 := by
  have hc := reflectedFellerTimeOperator_continuous L hL D g
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun t : ℝ => reflectedFellerIntegralOperator L hL D t g)
    (reflectedFellerTimeOperator L hL D 0 g) 0 at hd
  have hz : reflectedFellerTimeOperator L hL D 0 g = g := by
    simp only [reflectedFellerTimeOperator, mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero]
  rw [hz] at hd
  apply (hd.add_const f).hasDerivWithinAt.congr_of_mem
  · intro t ht
    exact sub_eq_iff_eq_add.mp (h t ht)
  · exact (le_refl (0 : ℝ))

theorem reflectedFeller_finite_cosine_evolution_derivative (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r : ℝ => reflectedFellerTimeOperator L hL D r
      (∑ n ∈ s, c n • neumannCosine L n))
      (reflectedFellerTimeOperator L hL D t
        (∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n)) (Ici 0) t := by
  have hd (n : ℕ) := (reflectedFellerOperator_cosine_derivative L hL D hD n t ht).const_smul (c n)
  have hh := HasDerivWithinAt.fun_sum (fun n (_ : n ∈ s) => hd n)
  simp only [Pi.smul_apply, smul_smul] at hh
  have he : (fun r : ℝ => reflectedFellerTimeOperator L hL D r
      (∑ n ∈ s, c n • neumannCosine L n)) =
      (fun r : ℝ => ∑ n ∈ s, c n • reflectedFellerOperator L hL
        (Real.toNNReal (2 * D * r)) (neumannCosine L n)) := by
    funext r
    simp only [reflectedFellerTimeOperator, map_sum, map_smul]
  rw [he]
  apply hh.congr_deriv
  simp only [reflectedFellerTimeOperator, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n _
  rw [reflectedFellerOperator_cosine_time L hL D hD n t ht, smul_smul]
  congr 1
  ring

theorem reflectedFeller_finite_cosine_integral (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerTimeOperator L hL D t (∑ n ∈ s, c n • neumannCosine L n) -
        ∑ n ∈ s, c n • neumannCosine L n =
      reflectedFellerIntegralOperator L hL D t
        (∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (reflectedFellerTimeOperator_continuous L hL D (∑ n ∈ s, c n • neumannCosine L n)).continuousOn
    (fun r hr => (reflectedFeller_finite_cosine_evolution_derivative L hL D hD s c r hr.1.le).mono
      (fun y hy => (hr.1.trans hy).le))
    ((reflectedFellerTimeOperator_continuous L hL D
      (∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n)).intervalIntegrable 0 t)
  simpa only [reflectedFellerIntegralOperator_apply, reflectedFellerTimeOperator,
    mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero] using he.symm

end TimeTraps.Probability

end
