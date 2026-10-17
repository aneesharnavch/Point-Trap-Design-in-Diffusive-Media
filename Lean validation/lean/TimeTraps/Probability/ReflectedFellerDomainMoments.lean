module

public import TimeTraps.Probability.ReflectedFellerDomainPairing

@[expose] public section

/-! Cosine moments of every actual uniform-norm generator pair follow
by applying bounded integral functionals to its right derivative. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedFeller_generator_cosine_moment (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (f g : C(Icc (0 : ℝ) L, ℝ))
    (hg : HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0)
    (n : ℕ) :
    reflectedFellerPairing L hL (neumannCosine L n) g =
      (-D * ((n : ℝ) * Real.pi / L) ^ 2) * reflectedFellerPairing L hL (neumannCosine L n) f := by
  have hc : HasDerivWithinAt (fun t : ℝ => reflectedFellerPairing L hL (neumannCosine L n)
      (reflectedFellerTimeOperator L hL D t f))
      (reflectedFellerPairing L hL (neumannCosine L n) g) (Ici 0) 0 := by
    simpa only [Function.comp_def] using
      (reflectedFellerPairing L hL (neumannCosine L n)).hasFDerivAt.comp_hasDerivWithinAt 0 hg
  have hd : HasDerivWithinAt (fun t : ℝ => Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t) *
      reflectedFellerPairing L hL (neumannCosine L n) f)
      ((-D * ((n : ℝ) * Real.pi / L) ^ 2) * reflectedFellerPairing L hL (neumannCosine L n) f)
      (Ici 0) 0 := by
    simpa only [id_eq, mul_one, mul_zero, Real.exp_zero, one_mul] using
      ((((hasDerivAt_id (0 : ℝ)).const_mul (-D * ((n : ℝ) * Real.pi / L) ^ 2)).exp).mul_const
        (reflectedFellerPairing L hL (neumannCosine L n) f)).hasDerivWithinAt
  have hd' := hd.congr_of_mem (fun t ht => reflectedFellerPairing_cosine_time L hL D hD n f t ht)
    (show (0 : ℝ) ∈ Ici 0 by simp)
  exact (hc.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hd'.derivWithin (uniqueDiffWithinAt_Ici 0))

theorem reflectedFeller_generator_mean_zero (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (f g : C(Icc (0 : ℝ) L, ℝ))
    (hg : HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0) :
    reflectedFellerMean L hL g = 0 := by
  have he := reflectedFeller_generator_cosine_moment L hL D hD f g hg 0
  simpa only [Nat.cast_zero, neumannCosine_zero, reflectedFellerPairing_apply,
    one_mul, zero_mul, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero] using he

end TimeTraps.Probability
