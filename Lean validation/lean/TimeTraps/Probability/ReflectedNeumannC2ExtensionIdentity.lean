module

public import TimeTraps.Probability.ReflectedNeumannC2ExtensionPrimitive

@[expose] public section

/-! The actual folded Neumann primitive is the global double primitive
of its folded mean-zero curvature. Equality is proved on the dense cosine
span and extended by bounded linearity, so it includes every fold corner. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedFellerRawPrimitive_cosine_global (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) (x : ℝ) :
    reflectedFellerRawPrimitive L hL (neumannCosine L n) x =
      Real.sin (((n : ℝ) * Real.pi / L) * x) / ((n : ℝ) * Real.pi / L) := by
  let a := (n : ℝ) * Real.pi / L
  have ha : a ≠ 0 := reflectedFeller_cosine_frequency_ne L hL n hn
  have hd (y : ℝ) : HasDerivAt (fun y => Real.sin (a * y) / a) (Real.cos (a * y)) y := by
    have h := (((hasDerivAt_id y).const_mul a).sin).div_const a
    simp only [id_eq, mul_one] at h
    apply h.congr_deriv
    field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun y _ => hd y) ((by fun_prop : Continuous (fun y : ℝ => Real.cos (a * y))).intervalIntegrable 0 x)
  unfold reflectedFellerRawPrimitive
  simp_rw [reflectedFellerExtension_cosine]
  simpa only [mul_zero, Real.sin_zero, zero_div, sub_zero] using he

theorem reflectedNeumannDoublePrimitive_cosine (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) (x : ℝ) :
    reflectedNeumannDoublePrimitive L hL (neumannCosine L n) x =
      (1 - Real.cos (((n : ℝ) * Real.pi / L) * x)) / (((n : ℝ) * Real.pi / L) ^ 2) := by
  let a := (n : ℝ) * Real.pi / L
  have ha : a ≠ 0 := reflectedFeller_cosine_frequency_ne L hL n hn
  have hd (y : ℝ) : HasDerivAt (fun y => (1 - Real.cos (a * y)) / a ^ 2)
      (Real.sin (a * y) / a) y := by
    have h := ((hasDerivAt_const y (1 : ℝ)).sub
      (((hasDerivAt_id y).const_mul a).cos)).div_const (a ^ 2)
    simp only [id_eq, mul_one, zero_sub] at h
    apply h.congr_deriv
    field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun y _ => hd y) ((by fun_prop : Continuous (fun y : ℝ => Real.sin (a * y) / a)).intervalIntegrable 0 x)
  unfold reflectedNeumannDoublePrimitive
  simp_rw [reflectedFellerRawPrimitive_cosine_global L hL n hn]
  simpa only [mul_zero, Real.cos_zero, sub_self, zero_div, sub_zero] using he

theorem reflectedFellerNeumannPrimitive_extension (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    reflectedFellerExtension L hL (reflectedFellerNeumannPrimitive L hL q) x =
      reflectedNeumannDoublePrimitive L hL (reflectedFellerMeanZero L hL q) x := by
  let A : C(Icc (0 : ℝ) L, ℝ) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ (reflectedIntervalFold L hL x)).comp (reflectedFellerNeumannPrimitive L hL)
  let B : C(Icc (0 : ℝ) L, ℝ) →L[ℝ] ℝ :=
    (reflectedNeumannDoublePrimitiveFunctional L hL x).comp (reflectedFellerMeanZero L hL)
  have hm : EqOn A.toLinearMap B.toLinearMap (Set.range (fun n : ℕ => neumannCosine L n)) := by
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      change reflectedFellerNeumannPrimitive L hL (neumannCosine L 0) (reflectedIntervalFold L hL x) =
        reflectedNeumannDoublePrimitiveFunctional L hL x (reflectedFellerMeanZero L hL (neumannCosine L 0))
      simp only [neumannCosine_zero, reflectedFellerNeumannPrimitive_apply,
        reflectedFellerMeanZero_one, map_zero, ContinuousMap.zero_apply]
    · change reflectedFellerNeumannPrimitive L hL (neumannCosine L n) (reflectedIntervalFold L hL x) =
        reflectedNeumannDoublePrimitive L hL (reflectedFellerMeanZero L hL (neumannCosine L n)) x
      rw [reflectedFellerNeumannPrimitive_apply, reflectedFellerMeanZero_cosine L hL n hn,
        reflectedFellerPrimitive_twice_cosine L hL n hn, reflectedNeumannDoublePrimitive_cosine L hL n hn]
      change (((n : ℝ) * Real.pi / L) ^ 2)⁻¹ *
        (1 - Real.cos (((n : ℝ) * Real.pi / L) * reflectedFold L x)) = _
      rw [reflectedFold_cosine L hL n x]
      ring
  have he : EqOn A B (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) := by
    intro u hu
    change u ∈ neumannCosineSpan L at hu
    rw [neumannCosineSpan_eq_natSpan] at hu
    exact LinearMap.eqOn_span hm hu
  have hd : Dense (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, neumannCosineAlgebra_dense L hL]
    rfl
  exact congrFun (Continuous.ext_on hd A.continuous B.continuous he) q

end TimeTraps.Probability
