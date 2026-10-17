module

public import TimeTraps.Interval.MediumOptimization
public import TimeTraps.Interval.GlobalOptimization

@[expose] public section

/-!
Medium ordering and certified robustness for the independent original weak
design space. The physical optimal value is defined using only the physical
essential norms, then identified with the source-partition minimum. Two
physical media may have different lengths or source masses, but their
normalized budgets K/S must agree and both use the full reflected interval
design class with the same count.
-/

namespace TimeTraps.Interval

open Set

variable {n : ℕ}

noncomputable def IntervalMedium.optimalValue (A : IntervalMedium) (n : ℕ) (K : ℝ) : ℝ :=
  sInf (range (fun D : IntervalDesign A n K => D.cost))

theorem IntervalMedium.optimalValue_eq_partition (A : IntervalMedium) (hn : 0 < n)
    {K : ℝ} (hK : 0 < K) :
    A.optimalValue n K = A.cellWeight.optimalValue n (div_pos hK A.source.mass_pos) := by
  obtain ⟨Q, hvalue, hmin⟩ := A.cellWeight.optimalValue_attained hn (div_pos hK A.source.mass_pos)
  have hD := A.construct_optimal Q hK (fun P => hmin P.closed)
  have hleast := (A.construct Q hK).optimal_iff_isLeast.mp hD
  change sInf (range (fun D : IntervalDesign A n K => D.cost)) = _
  rw [hleast.csInf_eq, A.construct_cost]
  exact hvalue.symm

theorem IntervalMedium.optimalValue_attained (A : IntervalMedium) (hn : 0 < n)
    {K : ℝ} (hK : 0 < K) :
    ∃ D : IntervalDesign A n K, D.Optimal ∧ D.cost = A.optimalValue n K := by
  obtain ⟨Q, hvalue, hmin⟩ := A.cellWeight.optimalValue_attained hn (div_pos hK A.source.mass_pos)
  refine ⟨A.construct Q hK, A.construct_optimal Q hK (fun P => hmin P.closed), ?_⟩
  rw [A.construct_cost, A.optimalValue_eq_partition hn hK]
  exact hvalue.symm

theorem IntervalMedium.optimalValue_mono_weight (A B : IntervalMedium) (hn : 0 < n)
    {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, A.cellWeight.value x ≤ B.cellWeight.value x) :
    A.optimalValue n K₁ ≤ B.optimalValue n K₂ := by
  rw [A.optimalValue_eq_partition hn hK₁, B.optimalValue_eq_partition hn hK₂]
  simp only [hbudget]
  exact A.cellWeight.optimalValue_mono_weight B.cellWeight hn hAB (div_pos hK₂ B.source.mass_pos)

theorem IntervalMedium.optimalValue_lt_weight (A B : IntervalMedium) (hn : 0 < n)
    {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, A.cellWeight.value x < B.cellWeight.value x) :
    A.optimalValue n K₁ < B.optimalValue n K₂ := by
  rw [A.optimalValue_eq_partition hn hK₁, B.optimalValue_eq_partition hn hK₂]
  simp only [hbudget]
  exact A.cellWeight.optimalValue_lt_weight B.cellWeight hn hAB (div_pos hK₂ B.source.mass_pos)

theorem IntervalMedium.optimalValue_abs_sub_le (A B : IntervalMedium) (hn : 0 < n)
    {K₁ K₂ ε : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, |A.cellWeight.value x - B.cellWeight.value x| ≤ ε) :
    |A.optimalValue n K₁ - B.optimalValue n K₂| ≤ ε / 2 := by
  rw [A.optimalValue_eq_partition hn hK₁, B.optimalValue_eq_partition hn hK₂]
  simp only [hbudget]
  exact A.cellWeight.optimalValue_abs_sub_le B.cellWeight hn hAB (div_pos hK₂ B.source.mass_pos)

theorem IntervalDesign.optimal_cost_mono_weight {A B : IntervalMedium}
    {K₁ K₂ : ℝ} (D : IntervalDesign A n K₁) (E : IntervalDesign B n K₂)
    (hD : D.Optimal) (hE : E.Optimal) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, A.cellWeight.value x ≤ B.cellWeight.value x) : D.cost ≤ E.cost := by
  have hd : A.optimalValue n K₁ = D.cost := (D.optimal_iff_isLeast.mp hD).csInf_eq
  have he : B.optimalValue n K₂ = E.cost := (E.optimal_iff_isLeast.mp hE).csInf_eq
  rw [← hd, ← he]
  exact A.optimalValue_mono_weight B D.partition.size_pos hK₁ hK₂ hbudget hAB

theorem IntervalDesign.optimal_cost_lt_weight {A B : IntervalMedium}
    {K₁ K₂ : ℝ} (D : IntervalDesign A n K₁) (E : IntervalDesign B n K₂)
    (hD : D.Optimal) (hE : E.Optimal) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, A.cellWeight.value x < B.cellWeight.value x) : D.cost < E.cost := by
  have hd : A.optimalValue n K₁ = D.cost := (D.optimal_iff_isLeast.mp hD).csInf_eq
  have he : B.optimalValue n K₂ = E.cost := (E.optimal_iff_isLeast.mp hE).csInf_eq
  rw [← hd, ← he]
  exact A.optimalValue_lt_weight B D.partition.size_pos hK₁ hK₂ hbudget hAB

theorem IntervalDesign.optimal_cost_abs_sub_le {A B : IntervalMedium}
    {K₁ K₂ ε : ℝ} (D : IntervalDesign A n K₁) (E : IntervalDesign B n K₂)
    (hD : D.Optimal) (hE : E.Optimal) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, |A.cellWeight.value x - B.cellWeight.value x| ≤ ε) :
    |D.cost - E.cost| ≤ ε / 2 := by
  have hd : A.optimalValue n K₁ = D.cost := (D.optimal_iff_isLeast.mp hD).csInf_eq
  have he : B.optimalValue n K₂ = E.cost := (E.optimal_iff_isLeast.mp hE).csInf_eq
  rw [← hd, ← he]
  exact A.optimalValue_abs_sub_le B D.partition.size_pos hK₁ hK₂ hbudget hAB

end TimeTraps.Interval
