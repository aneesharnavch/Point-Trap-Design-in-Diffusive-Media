module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-! Finite cosine sums on the actual closed interval form a unital real
algebra. Integer indices simplify product-to-sum; negative indices give
the same modes as their positive counterparts. -/

noncomputable section

namespace TimeTraps.Analysis

open Set

def neumannCosine (L : ℝ) (n : ℤ) : C(Icc (0 : ℝ) L, ℝ) where
  toFun x := Real.cos (((n : ℝ) * Real.pi / L) * x.val)
  continuous_toFun := Real.continuous_cos.comp
    (continuous_const.mul continuous_subtype_val)

theorem neumannCosine_zero (L : ℝ) : neumannCosine L 0 = 1 := by
  ext x
  simp [neumannCosine]

theorem neumannCosine_neg (L : ℝ) (n : ℤ) : neumannCosine L (-n) = neumannCosine L n := by
  ext x
  change Real.cos ((((-n : ℤ) : ℝ) * Real.pi / L) * x.val) = _
  rw [Int.cast_neg, neg_mul, neg_div, neg_mul, Real.cos_neg]
  rfl

theorem neumannCosine_mul (L : ℝ) (m n : ℤ) :
    neumannCosine L m * neumannCosine L n =
      (1 / 2 : ℝ) • (neumannCosine L (m - n) + neumannCosine L (m + n)) := by
  ext x
  change Real.cos (((m : ℝ) * Real.pi / L) * x.val) *
      Real.cos (((n : ℝ) * Real.pi / L) * x.val) =
    (1 / 2 : ℝ) * (Real.cos ((((m - n : ℤ) : ℝ) * Real.pi / L) * x.val) +
      Real.cos ((((m + n : ℤ) : ℝ) * Real.pi / L) * x.val))
  have he := Real.two_mul_cos_mul_cos (((m : ℝ) * Real.pi / L) * x.val)
    (((n : ℝ) * Real.pi / L) * x.val)
  rw [show (((m - n : ℤ) : ℝ) * Real.pi / L) * x.val =
    ((m : ℝ) * Real.pi / L) * x.val - ((n : ℝ) * Real.pi / L) * x.val by push_cast; ring,
    show (((m + n : ℤ) : ℝ) * Real.pi / L) * x.val =
    ((m : ℝ) * Real.pi / L) * x.val + ((n : ℝ) * Real.pi / L) * x.val by push_cast; ring]
  linarith

def neumannCosineSpan (L : ℝ) : Submodule ℝ C(Icc (0 : ℝ) L, ℝ) :=
  Submodule.span ℝ (Set.range (neumannCosine L))

theorem neumannCosineSpan_one (L : ℝ) : (1 : C(Icc (0 : ℝ) L, ℝ)) ∈ neumannCosineSpan L := by
  rw [← neumannCosine_zero L]
  exact Submodule.subset_span ⟨0, rfl⟩

theorem neumannCosineSpan_mul (L : ℝ) (f g : C(Icc (0 : ℝ) L, ℝ))
    (hf : f ∈ neumannCosineSpan L) (hg : g ∈ neumannCosineSpan L) :
    f * g ∈ neumannCosineSpan L := by
  refine Submodule.span_induction₂ (p := fun f g _ _ => f * g ∈ neumannCosineSpan L)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [neumannCosine_mul]
    exact (neumannCosineSpan L).smul_mem _ ((neumannCosineSpan L).add_mem
      (Submodule.subset_span ⟨m - n, rfl⟩) (Submodule.subset_span ⟨m + n, rfl⟩))
  · intro y _
    simpa only [zero_mul] using (neumannCosineSpan L).zero_mem
  · intro x _
    simpa only [mul_zero] using (neumannCosineSpan L).zero_mem
  · intro x y z _ _ _ hx hy
    rw [add_mul]
    exact (neumannCosineSpan L).add_mem hx hy
  · intro x y z _ _ _ hy hz
    rw [mul_add]
    exact (neumannCosineSpan L).add_mem hy hz
  · intro r x y _ _ hxy
    rw [smul_mul_assoc]
    exact (neumannCosineSpan L).smul_mem r hxy
  · intro r x y _ _ hxy
    rw [mul_smul_comm]
    exact (neumannCosineSpan L).smul_mem r hxy

def neumannCosineAlgebra (L : ℝ) : Subalgebra ℝ C(Icc (0 : ℝ) L, ℝ) :=
  (neumannCosineSpan L).toSubalgebra (neumannCosineSpan_one L) (neumannCosineSpan_mul L)

theorem neumannCosineAlgebra_mem (L : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) :
    f ∈ neumannCosineAlgebra L ↔ f ∈ neumannCosineSpan L := Iff.rfl

end TimeTraps.Analysis

end
