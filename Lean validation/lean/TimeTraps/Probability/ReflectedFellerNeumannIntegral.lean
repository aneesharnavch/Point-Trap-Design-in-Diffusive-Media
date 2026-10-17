module

public import TimeTraps.Probability.ReflectedFellerPrimitiveCosine

@[expose] public section

/-! The inverse of the zero-mean second derivative, as a bounded map on
continuous functions, satisfies the actual Feller variation identity.
The identity extends from cosine modes by continuity of both bounded
maps, rather than by an unsupported assertion about generator closure. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

def reflectedFellerNeumannPrimitive (L : ℝ) (hL : 0 < L) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) :=
  (reflectedFellerPrimitive L hL).comp
    ((reflectedFellerPrimitive L hL).comp (reflectedFellerMeanZero L hL))

theorem reflectedFellerNeumannPrimitive_apply (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerNeumannPrimitive L hL f = reflectedFellerPrimitive L hL
      (reflectedFellerPrimitive L hL (reflectedFellerMeanZero L hL f)) := rfl

theorem reflectedFellerNeumannPrimitive_cosine_integral (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerTimeOperator L hL D t (reflectedFellerNeumannPrimitive L hL (neumannCosine L n)) -
      reflectedFellerNeumannPrimitive L hL (neumannCosine L n) =
      reflectedFellerIntegralOperator L hL D t (D • reflectedFellerMeanZero L hL (neumannCosine L n)) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, neumannCosine_zero, reflectedFellerNeumannPrimitive_apply,
      reflectedFellerMeanZero_one, map_zero, smul_zero, sub_zero]
  let a := (n : ℝ) * Real.pi / L
  have ha : a ≠ 0 := reflectedFeller_cosine_frequency_ne L hL n hn
  have hone : reflectedFellerTimeOperator L hL D t 1 = 1 :=
    reflectedFellerOperator_one L hL _
  have he : reflectedFellerTimeOperator L hL D t (neumannCosine L n) - neumannCosine L n =
      reflectedFellerIntegralOperator L hL D t ((-D * a ^ 2) • neumannCosine L n) := by
    simpa only [Finset.sum_singleton, one_smul, one_mul] using
      reflectedFeller_finite_cosine_integral L hL D hD {n} (fun _ => 1) t ht
  rw [reflectedFellerNeumannPrimitive_apply, reflectedFellerMeanZero_cosine L hL n hn,
    reflectedFellerPrimitive_twice_cosine L hL n hn]
  change reflectedFellerTimeOperator L hL D t ((a ^ 2)⁻¹ • (1 - neumannCosine L n)) -
      (a ^ 2)⁻¹ • (1 - neumannCosine L n) =
    reflectedFellerIntegralOperator L hL D t (D • neumannCosine L n)
  calc
    _ = -(a ^ 2)⁻¹ • (reflectedFellerTimeOperator L hL D t (neumannCosine L n) -
        neumannCosine L n) := by
      rw [map_smul, map_sub, hone]
      module
    _ = _ := by
      rw [he, map_smul, smul_smul, map_smul]
      congr 1
      field_simp

theorem reflectedFellerNeumannPrimitive_integral (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerTimeOperator L hL D t (reflectedFellerNeumannPrimitive L hL f) -
      reflectedFellerNeumannPrimitive L hL f =
      reflectedFellerIntegralOperator L hL D t (D • reflectedFellerMeanZero L hL f) := by
  let A := (reflectedFellerTimeOperator L hL D t).comp (reflectedFellerNeumannPrimitive L hL) -
    reflectedFellerNeumannPrimitive L hL
  let B := (reflectedFellerIntegralOperator L hL D t).comp (D • reflectedFellerMeanZero L hL)
  have hm : EqOn A.toLinearMap B.toLinearMap (Set.range (fun n : ℕ => neumannCosine L n)) := by
    rintro _ ⟨n, rfl⟩
    exact reflectedFellerNeumannPrimitive_cosine_integral L hL D hD n t ht
  have he : EqOn A B (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) := by
    intro u hu
    change u ∈ neumannCosineSpan L at hu
    rw [neumannCosineSpan_eq_natSpan] at hu
    exact LinearMap.eqOn_span hm hu
  have hd : Dense (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, neumannCosineAlgebra_dense L hL]
    rfl
  exact congrFun (Continuous.ext_on hd A.continuous B.continuous he) f

theorem reflectedFellerNeumannPrimitive_generator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (f : C(Icc (0 : ℝ) L, ℝ)) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t
      (reflectedFellerNeumannPrimitive L hL f)) (D • reflectedFellerMeanZero L hL f) (Ici 0) 0 :=
  reflectedFeller_generator_of_integral L hL D _ _
    (reflectedFellerNeumannPrimitive_integral L hL D hD f)

end TimeTraps.Probability

end
