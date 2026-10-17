module

public import TimeTraps.Interval.PartitionComparison
public import TimeTraps.Interval.PartitionMinimum

@[expose] public section

/-!
Ordered-media and robustness theorems for optimized source partitions.
Both media use the identical admissible set and normalized budget. The
nonstrict comparison and robustness hold for any nonempty admissible set;
strictness uses attainment, which is proved on the full closed simplex.
-/

namespace TimeTraps.Interval

open Set

variable {n : ℕ}

noncomputable def CellWeight.optimalIn (W : CellWeight) (C : Set (ClosedPartition n))
    {b : ℝ} (hb : 0 < b) : ℝ := sInf ((fun Q => Q.root W hb) '' C)

theorem CellWeight.partitionValues_bddBelow (W : CellWeight) (C : Set (ClosedPartition n))
    {b : ℝ} (hb : 0 < b) : BddBelow ((fun Q => Q.root W hb) '' C) := by
  refine ⟨1 / b, ?_⟩
  rintro M ⟨Q, _, rfl⟩
  exact Q.root_lower W hb

theorem CellWeight.optimalIn_le_root (W : CellWeight) {C : Set (ClosedPartition n)}
    {b : ℝ} (hb : 0 < b) {Q : ClosedPartition n} (hQ : Q ∈ C) :
    W.optimalIn C hb ≤ Q.root W hb :=
  csInf_le (W.partitionValues_bddBelow C hb) ⟨Q, hQ, rfl⟩

theorem CellWeight.optimalIn_eq_of_minimizer (W : CellWeight) {C : Set (ClosedPartition n)}
    {b : ℝ} (hb : 0 < b) {Q : ClosedPartition n} (hQ : Q ∈ C)
    (hmin : ∀ P ∈ C, Q.root W hb ≤ P.root W hb) : W.optimalIn C hb = Q.root W hb := by
  apply IsLeast.csInf_eq
  refine ⟨⟨Q, hQ, rfl⟩, ?_⟩
  rintro M ⟨P, hP, rfl⟩
  exact hmin P hP

theorem CellWeight.optimalIn_mono_weight (W V : CellWeight)
    (C : Set (ClosedPartition n)) (hC : C.Nonempty)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {b : ℝ} (hb : 0 < b) : W.optimalIn C hb ≤ V.optimalIn C hb := by
  apply le_csInf (hC.image _)
  rintro M ⟨Q, hQ, rfl⟩
  exact (W.optimalIn_le_root hb hQ).trans (Q.root_mono_weight W V hWV hb)

theorem CellWeight.optimalIn_le_add_of_root_le_add (W V : CellWeight)
    (C : Set (ClosedPartition n)) (hC : C.Nonempty) {b ε : ℝ} (hb : 0 < b)
    (hWV : ∀ Q ∈ C, Q.root W hb ≤ Q.root V hb + ε) :
    W.optimalIn C hb ≤ V.optimalIn C hb + ε := by
  have h : W.optimalIn C hb - ε ≤ V.optimalIn C hb := by
    apply le_csInf (hC.image _)
    rintro M ⟨Q, hQ, rfl⟩
    have h₁ := W.optimalIn_le_root hb hQ
    have h₂ := hWV Q hQ
    linarith
  linarith

theorem CellWeight.optimalIn_abs_sub_le (W V : CellWeight)
    (C : Set (ClosedPartition n)) (hC : C.Nonempty)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    {b : ℝ} (hb : 0 < b) : |W.optimalIn C hb - V.optimalIn C hb| ≤ ε / 2 := by
  have hl := W.optimalIn_le_add_of_root_le_add V C hC hb (ε := ε / 2)
    (fun Q _ => by linarith [(abs_le.mp (Q.root_abs_sub_le W V hWV hb)).2])
  have hr := V.optimalIn_le_add_of_root_le_add W C hC hb (ε := ε / 2)
    (fun Q _ => by linarith [(abs_le.mp (Q.root_abs_sub_le W V hWV hb)).1])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem CellWeight.optimalIn_lt_weight_of_minimizer (W V : CellWeight)
    {C : Set (ClosedPartition n)}
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {b : ℝ} (hb : 0 < b) {Q : ClosedPartition n} (hQ : Q ∈ C)
    (hmin : ∀ P ∈ C, Q.root V hb ≤ P.root V hb) :
    W.optimalIn C hb < V.optimalIn C hb := by
  rw [V.optimalIn_eq_of_minimizer hb hQ hmin]
  exact (W.optimalIn_le_root hb hQ).trans_lt (Q.root_lt_weight W V hWV hb)

noncomputable def CellWeight.optimalValue (W : CellWeight) (n : ℕ)
    {b : ℝ} (hb : 0 < b) : ℝ := W.optimalIn (Set.univ : Set (ClosedPartition n)) hb

theorem CellWeight.optimalValue_attained (W : CellWeight) (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) :
    ∃ Q : StrictPartition n, W.optimalValue n hb = Q.closed.root W hb ∧
      ∀ P : ClosedPartition n, Q.closed.root W hb ≤ P.root W hb := by
  obtain ⟨Q, hQ⟩ := StrictPartition.minimum_exists W hn hb
  exact ⟨Q, W.optimalIn_eq_of_minimizer hb (mem_univ _) (fun P _ => hQ P), hQ⟩

theorem CellWeight.optimalValue_mono_weight (W V : CellWeight) (hn : 0 < n)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {b : ℝ} (hb : 0 < b) : W.optimalValue n hb ≤ V.optimalValue n hb :=
  W.optimalIn_mono_weight V univ ⟨(StrictPartition.uniform n hn).closed, mem_univ _⟩ hWV hb

theorem CellWeight.optimalValue_lt_weight (W V : CellWeight) (hn : 0 < n)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {b : ℝ} (hb : 0 < b) : W.optimalValue n hb < V.optimalValue n hb := by
  obtain ⟨Q, hQ⟩ := ClosedPartition.minimum_exists V hn hb
  exact W.optimalIn_lt_weight_of_minimizer V hWV hb (mem_univ Q) (fun P _ => hQ P)

theorem CellWeight.optimalValue_abs_sub_le (W V : CellWeight) (hn : 0 < n)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    {b : ℝ} (hb : 0 < b) : |W.optimalValue n hb - V.optimalValue n hb| ≤ ε / 2 :=
  W.optimalIn_abs_sub_le V univ ⟨(StrictPartition.uniform n hn).closed, mem_univ _⟩ hWV hb

end TimeTraps.Interval
