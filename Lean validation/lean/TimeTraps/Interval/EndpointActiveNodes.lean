module

public import TimeTraps.Interval.EndpointPhysicalState

@[expose] public section

/-! The active physical nodes in the architecture's fixed left-to-right
order. Inactive endpoints are omitted, and no interior node is omitted. -/

namespace TimeTraps.Interval

open scoped BigOperators Classical

def EndpointArchitecture.activeNode (A : EndpointArchitecture) (i : Fin A.count) :
    Fin (A.interiorCount + 2) :=
  ⟨i.val + (if A.leftReactive = true then 0 else 1), by
    have hi := i.isLt
    cases hl : A.leftReactive <;> cases hr : A.rightReactive <;>
      simp_all [count] <;> omega⟩

theorem EndpointArchitecture.activeNode_strictMono (A : EndpointArchitecture) :
    StrictMono A.activeNode := by
  intro i j hij
  change i.val + _ < j.val + _
  exact Nat.add_lt_add_right hij _

theorem EndpointArchitecture.activeNode_left (A : EndpointArchitecture) (i : Fin A.count)
    (hi : A.kind i = .leftEndpoint) : A.activeNode i = 0 := by
  obtain ⟨hl, hv⟩ := (A.kind_left_iff i).mp hi
  apply Fin.ext
  simp only [activeNode, hl, if_true, hv, Nat.add_zero, Fin.val_zero]

theorem EndpointArchitecture.activeNode_right (A : EndpointArchitecture) (i : Fin A.count)
    (hi : A.kind i = .rightEndpoint) : A.activeNode i = Fin.last (A.interiorCount + 1) := by
  obtain ⟨hr, hv⟩ := (A.kind_right_iff i).mp hi
  apply Fin.ext
  cases hl : A.leftReactive <;>
    simp only [count, hl, hr, Bool.toNat_false, Bool.toNat_true] at hv <;>
    simp [activeNode, hl] <;> omega

theorem EndpointArchitecture.activeNode_interior (A : EndpointArchitecture)
    (i : Fin A.interiorCount) : A.activeNode (A.interiorCell i) = trapNode i := by
  apply Fin.ext
  cases hl : A.leftReactive <;> simp [activeNode, interiorCell, hl, trapNode]
  omega

theorem EndpointArchitecture.inactiveNode (A : EndpointArchitecture)
    (v : Fin (A.interiorCount + 2)) (hv : ¬ ∃ i, A.activeNode i = v) :
    (A.leftReactive = false ∧ v = 0) ∨
      (A.rightReactive = false ∧ v = Fin.last (A.interiorCount + 1)) := by
  by_contra hn
  apply hv
  have hvl := v.isLt
  cases hl : A.leftReactive <;> cases hr : A.rightReactive
  · have hv0 : v.val ≠ 0 := by intro h; apply hn; exact Or.inl ⟨hl, Fin.ext h⟩
    have hv1 : v.val ≠ A.interiorCount + 1 := by intro h; apply hn; exact Or.inr ⟨hr, Fin.ext h⟩
    refine ⟨⟨v.val - 1, ?_⟩, ?_⟩
    · simp only [count, hl, hr, Bool.toNat_false, Nat.add_zero]
      omega
    · apply Fin.ext
      simp [activeNode, hl]
      omega
  · have hv0 : v.val ≠ 0 := by intro h; apply hn; exact Or.inl ⟨hl, Fin.ext h⟩
    refine ⟨⟨v.val - 1, ?_⟩, ?_⟩
    · simp only [count, hl, hr, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
      omega
    · apply Fin.ext
      simp [activeNode, hl]
      omega
  · have hv1 : v.val ≠ A.interiorCount + 1 := by intro h; apply hn; exact Or.inr ⟨hr, Fin.ext h⟩
    refine ⟨⟨v.val, ?_⟩, ?_⟩
    · simp only [count, hl, hr, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
      omega
    · apply Fin.ext
      simp [activeNode, hl]
  · refine ⟨⟨v.val, ?_⟩, ?_⟩
    · simp only [count, hl, hr, Bool.toNat_true]
      omega
    · apply Fin.ext
      simp [activeNode, hl]

theorem EndpointArchitecture.sum_active (A : EndpointArchitecture)
    (f : Fin (A.interiorCount + 2) → ℝ)
    (hl : A.leftReactive = false → f 0 = 0)
    (hr : A.rightReactive = false → f (Fin.last (A.interiorCount + 1)) = 0) :
    (∑ i, f (A.activeNode i)) = ∑ v, f v := by
  calc
    _ = ∑ v ∈ Finset.univ.image A.activeNode, f v :=
      (Finset.sum_image (fun i _ j _ h => A.activeNode_strictMono.injective h)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      have hn : ¬ ∃ i, A.activeNode i = v := by simpa only [Finset.mem_image, Finset.mem_univ,
        true_and] using hv
      rcases A.inactiveNode v hn with ⟨h, rfl⟩ | ⟨h, rfl⟩
      · exact hl h
      · exact hr h

variable {A : EndpointArchitecture} {K : ℝ}

def EndpointReactions.activeStrength (R : EndpointReactions A K) (i : Fin A.count) : ℝ :=
  R.nodal (A.activeNode i)

theorem EndpointReactions.activeStrength_pos (R : EndpointReactions A K) (i : Fin A.count) :
    0 < R.activeStrength i := by
  cases hi : A.kind i with
  | ordinary =>
    obtain ⟨j, rfl⟩ := A.ordinary_is_interiorCell i hi
    simpa only [activeStrength, A.activeNode_interior, R.nodal_interior] using R.interior_pos j
  | leftEndpoint =>
    simpa only [activeStrength, A.activeNode_left i hi, R.nodal_first] using
      R.left_pos ((A.kind_left_iff i).mp hi).1
  | rightEndpoint =>
    simpa only [activeStrength, A.activeNode_right i hi, R.nodal_last] using
      R.right_pos ((A.kind_right_iff i).mp hi).1

theorem EndpointReactions.active_pairing (R : EndpointReactions A K)
    (U : Fin (A.interiorCount + 2) → ℝ) :
    (∑ i, R.activeStrength i * U (A.activeNode i)) = ∑ v, R.nodal v * U v := by
  apply A.sum_active (fun v => R.nodal v * U v)
  · intro h
    rw [R.nodal_first, R.left_zero h, zero_mul]
  · intro h
    rw [R.nodal_last, R.right_zero h, zero_mul]

theorem EndpointReactions.activeStrength_sum (R : EndpointReactions A K) :
    (∑ i, R.activeStrength i) = K := by
  have h := R.active_pairing (fun _ => 1)
  simpa only [mul_one, R.nodal_sum] using h

end TimeTraps.Interval
