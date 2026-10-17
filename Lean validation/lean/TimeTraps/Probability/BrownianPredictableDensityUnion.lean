module

public import TimeTraps.Probability.BrownianPredictableDensityIndicator

@[expose] public section

/-! Finite disjoint unions and their pointwise limits for predictable
cutoff indicators. The common finite-horizon bound is integrable in L2. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter Function
open scoped NNReal ENNReal Topology

variable {Ω : Type*}

theorem brownianPredictableCutoffIndicator_finset_union (T : ℝ≥0)
    (E : ℕ → Set (ℝ≥0 × Ω)) (hd : Pairwise (Disjoint on E)) (s : Finset ℕ) :
    brownianPredictableCutoffIndicator T (⋃ i ∈ s, E i) =
      ∑ i ∈ s, brownianPredictableCutoffIndicator T (E i) := by
  classical
  funext p
  simp only [brownianPredictableCutoffIndicator, brownianSquareProcess, Finset.sum_apply]
  rw [← Finset.mul_sum]
  congr 1
  by_cases h : ∃ i ∈ s, (p.1.toNNReal, p.2) ∈ E i
  · obtain ⟨i, hi, hip⟩ := h
    have hu : (p.1.toNNReal, p.2) ∈ ⋃ i ∈ s, E i := mem_iUnion₂.mpr ⟨i, hi, hip⟩
    rw [indicator_of_mem hu]
    symm
    calc
      _ = (E i).indicator (fun _ => (1 : ℝ)) (p.1.toNNReal, p.2) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          apply indicator_of_notMem
          intro hjp
          exact Set.disjoint_left.mp (hd hji) hjp hip
        · intro hni
          exact (hni hi).elim
      _ = 1 := indicator_of_mem hip _
  · rw [indicator_of_notMem (by simpa only [mem_iUnion, exists_prop] using h)]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact indicator_of_notMem (fun hip => h ⟨i, hi, hip⟩) _

theorem brownianPredictableCutoffIndicator_bound (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω)) (p : ℝ × Ω) :
    |brownianPredictableCutoffIndicator T E p| ≤ brownianPredictableCutoffIndicator T univ p := by
  simp only [brownianPredictableCutoffIndicator, brownianSquareProcess, indicator_univ]
  change |(Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 *
      E.indicator (fun _ => (1 : ℝ)) (p.1.toNNReal, p.2)| ≤
    (Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 * 1
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · rw [indicator_of_mem ht, one_mul, one_mul]
    by_cases hE : (p.1.toNNReal, p.2) ∈ E
    · rw [indicator_of_mem hE, abs_one]
    · rw [indicator_of_notMem hE, abs_zero]
      exact zero_le_one
  · rw [indicator_of_notMem ht, zero_mul, zero_mul, abs_zero]

theorem brownianPredictableCutoffIndicator_union_tendsto (T : ℝ≥0)
    (E : ℕ → Set (ℝ≥0 × Ω)) (p : ℝ × Ω) :
    Tendsto (fun n => brownianPredictableCutoffIndicator T (⋃ i ∈ Finset.range n, E i) p)
      atTop (𝓝 (brownianPredictableCutoffIndicator T (⋃ i, E i) p)) := by
  classical
  by_cases h : (p.1.toNNReal, p.2) ∈ ⋃ i, E i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp h
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    have hni : i ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have hu : (p.1.toNNReal, p.2) ∈ ⋃ i ∈ Finset.range n, E i :=
      mem_iUnion₂.mpr ⟨i, hni, hi⟩
    simp only [brownianPredictableCutoffIndicator, brownianSquareProcess,
      indicator_of_mem h, indicator_of_mem hu]
  · apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro n
    have hn : (p.1.toNNReal, p.2) ∉ ⋃ i ∈ Finset.range n, E i := by
      intro hp
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hp
      exact h (mem_iUnion.mpr ⟨i, hi⟩)
    simp only [brownianPredictableCutoffIndicator, brownianSquareProcess,
      indicator_of_notMem h, indicator_of_notMem hn]

end TimeTraps.Probability
