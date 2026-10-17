module

public import TimeTraps.Probability.ReflectedFellerDomainReconstruction
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Global double primitives of folded continuous data. The primitive
is C² on the whole real line by ordinary FTC. Evaluation at any real
point is a bounded linear functional of the original interval data. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set
open scoped ContDiff

def reflectedNeumannDoublePrimitive (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) : ℝ :=
  ∫ y in 0..x, reflectedFellerRawPrimitive L hL q y

theorem reflectedNeumannDoublePrimitive_derivative (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    HasDerivAt (reflectedNeumannDoublePrimitive L hL q) (reflectedFellerRawPrimitive L hL q x) x := by
  have hc := reflectedFellerRawPrimitive_continuous L hL q
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem reflectedNeumannDoublePrimitive_deriv (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) :
    deriv (reflectedNeumannDoublePrimitive L hL q) = reflectedFellerRawPrimitive L hL q :=
  funext (fun x => (reflectedNeumannDoublePrimitive_derivative L hL q x).deriv)

theorem reflectedNeumannDoublePrimitive_second (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) :
    deriv (deriv (reflectedNeumannDoublePrimitive L hL q)) = reflectedFellerExtension L hL q := by
  rw [reflectedNeumannDoublePrimitive_deriv]
  exact funext (fun x => (reflectedFellerRawPrimitive_derivative L hL q x).deriv)

theorem reflectedNeumannDoublePrimitive_contDiff (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) : ContDiff ℝ 2 (reflectedNeumannDoublePrimitive L hL q) := by
  have hraw : ContDiff ℝ 1 (reflectedFellerRawPrimitive L hL q) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (reflectedFellerRawPrimitive_derivative L hL q x).differentiableAt, ?_⟩
    have he : deriv (reflectedFellerRawPrimitive L hL q) = reflectedFellerExtension L hL q :=
      funext (fun x => (reflectedFellerRawPrimitive_derivative L hL q x).deriv)
    rw [he]
    exact (reflectedFellerExtension L hL q).continuous
  apply (contDiff_succ_iff_deriv (n := (1 : ℕ∞ω))).mpr
  refine ⟨fun x => (reflectedNeumannDoublePrimitive_derivative L hL q x).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [reflectedNeumannDoublePrimitive_deriv]
    exact hraw

theorem reflectedFellerRawPrimitive_norm (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    ‖reflectedFellerRawPrimitive L hL q x‖ ≤ |x| * ‖q‖ := by
  change ‖∫ y in 0..x, reflectedFellerExtension L hL q y‖ ≤ |x| * ‖q‖
  simpa only [sub_zero, mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := x) (fun y _ => reflectedFellerExtension_bound L hL q y)

theorem reflectedNeumannDoublePrimitive_norm (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    ‖reflectedNeumannDoublePrimitive L hL q x‖ ≤ |x| ^ 2 * ‖q‖ := by
  have hb (y : ℝ) (hy : y ∈ uIoc (0 : ℝ) x) : ‖reflectedFellerRawPrimitive L hL q y‖ ≤ |x| * ‖q‖ := by
    have hyb : |y| ≤ |x| := abs_le.mpr
      ⟨(le_min (neg_nonpos.mpr (abs_nonneg x)) (neg_abs_le x)).trans hy.1.le,
        hy.2.trans (max_le (abs_nonneg x) (le_abs_self x))⟩
    exact (reflectedFellerRawPrimitive_norm L hL q y).trans
      (mul_le_mul_of_nonneg_right hyb (norm_nonneg q))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) hb
  change ‖reflectedNeumannDoublePrimitive L hL q x‖ ≤ (|x| * ‖q‖) * |x - 0| at h
  calc
    _ ≤ (|x| * ‖q‖) * |x - 0| := h
    _ = _ := by rw [sub_zero]; ring

def reflectedNeumannDoublePrimitiveLinear (L : ℝ) (hL : 0 < L) (x : ℝ) :
    C(Icc (0 : ℝ) L, ℝ) →ₗ[ℝ] ℝ where
  toFun q := reflectedNeumannDoublePrimitive L hL q x
  map_add' q r := by
    have he (y : ℝ) : reflectedFellerRawPrimitive L hL (q + r) y =
        reflectedFellerRawPrimitive L hL q y + reflectedFellerRawPrimitive L hL r y := by
      change (∫ z in 0..y, reflectedFellerExtension L hL q z + reflectedFellerExtension L hL r z) = _
      exact intervalIntegral.integral_add ((reflectedFellerExtension L hL q).continuous.intervalIntegrable 0 y)
        ((reflectedFellerExtension L hL r).continuous.intervalIntegrable 0 y)
    unfold reflectedNeumannDoublePrimitive
    simp only [he]
    exact intervalIntegral.integral_add
      ((reflectedFellerRawPrimitive_continuous L hL q).intervalIntegrable 0 x)
      ((reflectedFellerRawPrimitive_continuous L hL r).intervalIntegrable 0 x)
  map_smul' c q := by
    have he (y : ℝ) : reflectedFellerRawPrimitive L hL (c • q) y =
        c • reflectedFellerRawPrimitive L hL q y :=
      intervalIntegral.integral_smul c _
    unfold reflectedNeumannDoublePrimitive
    simp only [he]
    exact intervalIntegral.integral_smul c _

def reflectedNeumannDoublePrimitiveFunctional (L : ℝ) (hL : 0 < L) (x : ℝ) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] ℝ :=
  (reflectedNeumannDoublePrimitiveLinear L hL x).mkContinuous (|x| ^ 2)
    (fun q => reflectedNeumannDoublePrimitive_norm L hL q x)

theorem reflectedNeumannDoublePrimitiveFunctional_apply (L : ℝ) (hL : 0 < L) (x : ℝ)
    (q : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedNeumannDoublePrimitiveFunctional L hL x q = reflectedNeumannDoublePrimitive L hL q x := rfl

end TimeTraps.Probability

end
