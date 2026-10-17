module

public import TimeTraps.Interval.EndpointCell

@[expose] public section

/-!
An independent mixed architecture: m interior traps, two endpoint-presence
flags, and a positive active count. The ordered cells contain the left
endpoint first, the m ordinary cells next, and the right endpoint last.
No interior trap is required when at least one endpoint is active.
-/

namespace TimeTraps.Interval

structure EndpointArchitecture where
  interiorCount : ℕ
  leftReactive : Bool
  rightReactive : Bool
  active_pos : 0 < interiorCount + leftReactive.toNat + rightReactive.toNat

def EndpointArchitecture.count (A : EndpointArchitecture) : ℕ :=
  A.interiorCount + A.leftReactive.toNat + A.rightReactive.toNat

theorem EndpointArchitecture.count_pos (A : EndpointArchitecture) : 0 < A.count :=
  A.active_pos

def EndpointArchitecture.kind (A : EndpointArchitecture) (i : Fin A.count) : CellKind :=
  if A.leftReactive = true ∧ i.val = 0 then .leftEndpoint
  else if A.rightReactive = true ∧ i.val + 1 = A.count then .rightEndpoint
  else .ordinary

theorem EndpointArchitecture.kind_left_iff (A : EndpointArchitecture) (i : Fin A.count) :
    A.kind i = .leftEndpoint ↔ A.leftReactive = true ∧ i.val = 0 := by
  unfold kind
  split_ifs <;> simp_all

theorem EndpointArchitecture.kind_right_iff (A : EndpointArchitecture) (i : Fin A.count) :
    A.kind i = .rightEndpoint ↔ A.rightReactive = true ∧ i.val + 1 = A.count := by
  have hdisjoint : ¬ (A.leftReactive = true ∧ i.val = 0) ∨
      ¬ (A.rightReactive = true ∧ i.val + 1 = A.count) := by
    by_cases hleft : A.leftReactive = true ∧ i.val = 0
    · right
      rintro ⟨hright, hi⟩
      simp only [count, hleft.1, hright, Bool.toNat_true] at hi
      omega
    · exact Or.inl hleft
  unfold kind
  split_ifs <;> simp_all

theorem EndpointArchitecture.kind_ordinary_iff (A : EndpointArchitecture) (i : Fin A.count) :
    A.kind i = .ordinary ↔
      A.leftReactive.toNat ≤ i.val ∧ i.val < A.leftReactive.toNat + A.interiorCount := by
  have hi := i.isLt
  unfold kind
  cases hleft : A.leftReactive <;> cases hright : A.rightReactive <;>
    simp only [count, hleft, hright, Bool.toNat_false, Bool.toNat_true] at hi ⊢ <;>
    split_ifs <;> simp_all <;> omega

def EndpointArchitecture.interiorCell (A : EndpointArchitecture) (i : Fin A.interiorCount) :
    Fin A.count :=
  ⟨A.leftReactive.toNat + i.val, by have hi := i.isLt; unfold count; omega⟩

theorem EndpointArchitecture.kind_interiorCell (A : EndpointArchitecture)
    (i : Fin A.interiorCount) : A.kind (A.interiorCell i) = .ordinary := by
  apply (A.kind_ordinary_iff _).mpr
  have hi := i.isLt
  simp only [interiorCell]
  omega

theorem EndpointArchitecture.interiorCell_injective (A : EndpointArchitecture) :
    Function.Injective A.interiorCell := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simpa only [interiorCell, Nat.add_left_cancel_iff] using h

theorem EndpointArchitecture.ordinary_is_interiorCell (A : EndpointArchitecture)
    (i : Fin A.count) (hi : A.kind i = .ordinary) :
    ∃ j : Fin A.interiorCount, A.interiorCell j = i := by
  obtain ⟨hl, hr⟩ := (A.kind_ordinary_iff i).mp hi
  refine ⟨⟨i.val - A.leftReactive.toNat, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [interiorCell]
  omega

def EndpointArchitecture.leftOnly : EndpointArchitecture := ⟨0, true, false, by decide⟩

def EndpointArchitecture.rightOnly : EndpointArchitecture := ⟨0, false, true, by decide⟩

def EndpointArchitecture.bothOnly : EndpointArchitecture := ⟨0, true, true, by decide⟩

theorem EndpointArchitecture.leftOnly_count : EndpointArchitecture.leftOnly.count = 1 := rfl

theorem EndpointArchitecture.rightOnly_count : EndpointArchitecture.rightOnly.count = 1 := rfl

theorem EndpointArchitecture.bothOnly_count : EndpointArchitecture.bothOnly.count = 2 := rfl

theorem EndpointArchitecture.leftOnly_kind (i : Fin EndpointArchitecture.leftOnly.count) :
    EndpointArchitecture.leftOnly.kind i = .leftEndpoint := by
  apply (EndpointArchitecture.leftOnly.kind_left_iff i).mpr
  exact ⟨rfl, by have hi := i.isLt; change i.val < 1 at hi; omega⟩

theorem EndpointArchitecture.rightOnly_kind (i : Fin EndpointArchitecture.rightOnly.count) :
    EndpointArchitecture.rightOnly.kind i = .rightEndpoint := by
  apply (EndpointArchitecture.rightOnly.kind_right_iff i).mpr
  exact ⟨rfl, by have hi := i.isLt; change i.val < 1 at hi; change i.val + 1 = 1; omega⟩

theorem EndpointArchitecture.bothOnly_kind (i : Fin EndpointArchitecture.bothOnly.count) :
    EndpointArchitecture.bothOnly.kind i =
      if i.val = 0 then .leftEndpoint else .rightEndpoint := by
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    exact (EndpointArchitecture.bothOnly.kind_left_iff i).mpr ⟨rfl, hi⟩
  · rw [if_neg hi]
    apply (EndpointArchitecture.bothOnly.kind_right_iff i).mpr
    exact ⟨rfl, by have h := i.isLt; change i.val < 2 at h; change i.val + 1 = 2; omega⟩

end TimeTraps.Interval
