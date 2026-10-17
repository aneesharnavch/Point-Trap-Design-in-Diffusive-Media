module

public import TimeTraps.Analysis.NeumannCosineAlgebra

@[expose] public section

/-! Uniform completeness of the natural Neumann cosine modes on `[0,L]`.
The first mode separates points, and product-to-sum makes their finite
linear span an algebra, so Stone-Weierstrass applies on the actual interval. -/

namespace TimeTraps.Analysis

open Set

theorem neumannCosineSpan_eq_natSpan (L : ℝ) :
    neumannCosineSpan L = Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · exact Submodule.subset_span ⟨k, rfl⟩
    · rw [neumannCosine_neg]
      exact Submodule.subset_span ⟨k, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Submodule.subset_span ⟨(n : ℤ), rfl⟩

theorem neumannCosineAlgebra_separatesPoints (L : ℝ) (hL : 0 < L) :
    (neumannCosineAlgebra L).SeparatesPoints := by
  intro x y hxy
  refine ⟨neumannCosine L 1, ⟨neumannCosine L 1, ?_, rfl⟩, ?_⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · intro he
    have hpos : 0 < Real.pi / L := div_pos Real.pi_pos hL
    have ha (z : Icc (0 : ℝ) L) : Real.pi / L * z.val ∈ Icc 0 Real.pi := by
      refine ⟨mul_nonneg hpos.le z.property.1, ?_⟩
      calc
        Real.pi / L * z.val ≤ Real.pi / L * L := mul_le_mul_of_nonneg_left z.property.2 hpos.le
        _ = Real.pi := div_mul_cancel₀ _ hL.ne'
    have hecos : Real.cos (Real.pi / L * x.val) = Real.cos (Real.pi / L * y.val) := by
      simpa only [neumannCosine, Int.cast_one, one_mul, ContinuousMap.coe_mk] using he
    apply hxy
    apply Subtype.ext
    exact mul_left_cancel₀ hpos.ne' (Real.injOn_cos (ha x) (ha y) hecos)

theorem neumannCosineAlgebra_dense (L : ℝ) (hL : 0 < L) :
    (neumannCosineAlgebra L).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (neumannCosineAlgebra_separatesPoints L hL)

theorem neumannCosine_uniform_approximation (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n)), ‖g - f‖ < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (neumannCosineAlgebra L) (neumannCosineAlgebra_separatesPoints L hL) f ε hε
  refine ⟨g, ?_, hg⟩
  rw [← neumannCosineSpan_eq_natSpan]
  exact g.property

end TimeTraps.Analysis
