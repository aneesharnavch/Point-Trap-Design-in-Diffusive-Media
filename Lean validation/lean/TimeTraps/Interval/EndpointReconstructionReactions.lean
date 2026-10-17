module

public import TimeTraps.Interval.EndpointActiveNodes

@[expose] public section

/-! Transfer any positive active strength vector into the independent
physical endpoint/interior reaction data, preserving the exact budget.
Inactive endpoints receive zero and endpoint-only architectures are included. -/

namespace TimeTraps.Interval

open scoped BigOperators Classical

noncomputable def EndpointArchitecture.activeLift (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (v : Fin (A.interiorCount + 2)) : ℝ :=
  ∑ i, if A.activeNode i = v then κ i else 0

theorem EndpointArchitecture.activeLift_active (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (i : Fin A.count) : A.activeLift κ (A.activeNode i) = κ i := by
  unfold activeLift
  simp only [A.activeNode_strictMono.injective.eq_iff]
  simp

theorem EndpointArchitecture.activeLift_interior (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (i : Fin A.interiorCount) :
    A.activeLift κ (trapNode i) = κ (A.interiorCell i) := by
  rw [← A.activeNode_interior, A.activeLift_active]

theorem EndpointArchitecture.activeLift_left_zero (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (hl : A.leftReactive = false) : A.activeLift κ 0 = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hn : A.activeNode i ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [activeNode, hl] at hv
  exact if_neg hn

theorem EndpointArchitecture.activeLift_right_zero (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (hr : A.rightReactive = false) :
    A.activeLift κ (Fin.last (A.interiorCount + 1)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hn : A.activeNode i ≠ Fin.last (A.interiorCount + 1) := by
    intro h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    cases hl : A.leftReactive <;> simp [activeNode, hl, count, hr] at hv hi <;> omega
  exact if_neg hn

theorem EndpointArchitecture.activeLift_left_pos (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (hκ : ∀ i, 0 < κ i) (hl : A.leftReactive = true) :
    0 < A.activeLift κ 0 := by
  let i : Fin A.count := ⟨0, A.count_pos⟩
  have hi : A.activeNode i = 0 := by
    apply Fin.ext
    simp [activeNode, hl, i]
  rw [← hi, A.activeLift_active]
  exact hκ i

theorem EndpointArchitecture.activeLift_right_pos (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (hκ : ∀ i, 0 < κ i) (hr : A.rightReactive = true) :
    0 < A.activeLift κ (Fin.last (A.interiorCount + 1)) := by
  let i : Fin A.count := ⟨A.count - 1, by have := A.count_pos; omega⟩
  have hk : A.kind i = .rightEndpoint :=
    (A.kind_right_iff i).mpr ⟨hr, by dsimp [i]; have := A.count_pos; omega⟩
  rw [← A.activeNode_right i hk, A.activeLift_active]
  exact hκ i

theorem EndpointArchitecture.activeLift_sum (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) : (∑ v, A.activeLift κ v) = ∑ i, κ i := by
  unfold activeLift
  rw [Finset.sum_comm]
  simp

theorem EndpointArchitecture.activeLift_split (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) :
    A.activeLift κ 0 + (∑ i, A.activeLift κ (trapNode i)) +
      A.activeLift κ (Fin.last (A.interiorCount + 1)) = ∑ i, κ i := by
  have hs := A.activeLift_sum κ
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hs
  simpa only [trapNode, Fin.succ_castSucc, Fin.succ_last, add_assoc, add_comm, add_left_comm] using hs

noncomputable def EndpointReactions.ofActive (A : EndpointArchitecture) (κ : Fin A.count → ℝ)
    (hκ : ∀ i, 0 < κ i) {K : ℝ} (hsum : ∑ i, κ i = K) : EndpointReactions A K where
  interiorStrength i := A.activeLift κ (trapNode i)
  leftStrength := A.activeLift κ 0
  rightStrength := A.activeLift κ (Fin.last (A.interiorCount + 1))
  interior_pos i := by rw [A.activeLift_interior]; exact hκ _
  left_condition := by
    cases hl : A.leftReactive
    · simpa only [hl, Bool.false_eq_true, if_false] using A.activeLift_left_zero κ hl
    · simpa only [hl, if_true] using A.activeLift_left_pos κ hκ hl
  right_condition := by
    cases hr : A.rightReactive
    · simpa only [hr, Bool.false_eq_true, if_false] using A.activeLift_right_zero κ hr
    · simpa only [hr, if_true] using A.activeLift_right_pos κ hκ hr
  total_strength := (A.activeLift_split κ).trans hsum

theorem EndpointReactions.ofActive_nodal (A : EndpointArchitecture) (κ : Fin A.count → ℝ)
    (hκ : ∀ i, 0 < κ i) {K : ℝ} (hsum : ∑ i, κ i = K)
    (v : Fin (A.interiorCount + 2)) :
    (EndpointReactions.ofActive A κ hκ hsum).nodal v = A.activeLift κ v := by
  refine Fin.cases rfl (fun j => ?_) v
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [nodal, ofActive]
  · simp [nodal, ofActive, trapNode]

theorem EndpointReactions.ofActive_activeStrength (A : EndpointArchitecture)
    (κ : Fin A.count → ℝ) (hκ : ∀ i, 0 < κ i) {K : ℝ} (hsum : ∑ i, κ i = K)
    (i : Fin A.count) : (EndpointReactions.ofActive A κ hκ hsum).activeStrength i = κ i := by
  rw [activeStrength, ofActive_nodal, A.activeLift_active]

end TimeTraps.Interval
