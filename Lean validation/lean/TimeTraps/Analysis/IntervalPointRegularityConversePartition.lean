module

public import TimeTraps.Analysis.IntervalPointRegularityPartition
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Every finite family of physical contacts admits a strict partition.
Coincident sites are merged as nodes; all original contact labels remain
in the assignment, so their physical strengths are still aggregated. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def UnitPointProblem.contactNodeSet (P : UnitPointProblem ι) : Finset ℝ :=
  insert 0 (insert 1 (Finset.univ.image P.site))

theorem UnitPointProblem.contactNodeSet_mem (P : UnitPointProblem ι) {x : ℝ}
    (hx : x ∈ P.contactNodeSet) : x ∈ Icc (0 : ℝ) 1 := by
  classical
  simp only [contactNodeSet, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hx
  rcases hx with rfl | rfl | ⟨i, rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact P.site_mem i

theorem UnitPointProblem.contactNodeSet_card (P : UnitPointProblem ι) :
    2 ≤ P.contactNodeSet.card := by
  classical
  have hs : ({0, 1} : Finset ℝ) ⊆ P.contactNodeSet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [contactNodeSet]
  simpa using Finset.card_le_card hs

theorem UnitPointProblem.exists_partition (P : UnitPointProblem ι) :
    ∃ n : ℕ, Nonempty (UnitPointPartition P n) := by
  classical
  let s := P.contactNodeSet
  let n := s.card - 2
  have hcard : s.card = n + 2 := by
    dsimp [n]
    exact (Nat.sub_add_cancel P.contactNodeSet_card).symm
  let q : Fin (n + 2) ↪o ℝ := s.orderEmbOfFin hcard
  have hmem (v : Fin (n + 2)) : q v ∈ s := s.orderEmbOfFin_mem hcard v
  have hrange : Set.range q = (s : Set ℝ) := s.range_orderEmbOfFin hcard
  have hzero : (0 : ℝ) ∈ s := by simp [s, contactNodeSet]
  have hone : (1 : ℝ) ∈ s := by simp [s, contactNodeSet]
  have h₀ : q 0 = 0 := by
    obtain ⟨v, hv⟩ := (show (0 : ℝ) ∈ Set.range q by rw [hrange]; exact hzero)
    apply le_antisymm
    · exact (q.monotone (Fin.zero_le v)).trans_eq hv
    · exact (P.contactNodeSet_mem (hmem 0)).1
  have h₁ : q (Fin.last (n + 1)) = 1 := by
    obtain ⟨v, hv⟩ := (show (1 : ℝ) ∈ Set.range q by rw [hrange]; exact hone)
    apply le_antisymm
    · exact (P.contactNodeSet_mem (hmem _)).2
    · exact hv.symm.trans_le (q.monotone (Fin.le_last v))
  have hsite (i : ι) : ∃ v, q v = P.site i := by
    change P.site i ∈ Set.range q
    rw [hrange]
    simp [s, contactNodeSet]
  choose node hnode using hsite
  exact ⟨n, ⟨⟨q, q.strictMono, h₀, h₁, node, fun i => (hnode i).symm⟩⟩⟩

end TimeTraps.Analysis
