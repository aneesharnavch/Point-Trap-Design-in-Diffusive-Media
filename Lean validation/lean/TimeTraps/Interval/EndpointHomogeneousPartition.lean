module

public import TimeTraps.Interval.EndpointConverse
public import TimeTraps.Interval.BudgetMoment
public import TimeTraps.Analysis.CubicMoment

@[expose] public section

/-! The homogeneous mixed partition has shares proportional to the number
of sides of each cell: two for ordinary cells and one for reactive ends. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators Classical

def EndpointArchitecture.sideCount (A : EndpointArchitecture) (i : Fin A.count) : ℝ :=
  if A.kind i = .ordinary then 2 else 1

def EndpointArchitecture.sideTotal (A : EndpointArchitecture) : ℝ := ∑ i, A.sideCount i

theorem EndpointArchitecture.sideCount_pos (A : EndpointArchitecture) (i : Fin A.count) :
    0 < A.sideCount i := by unfold sideCount; split_ifs <;> norm_num

theorem EndpointArchitecture.sideCount_interior (A : EndpointArchitecture) (j : Fin A.interiorCount) :
    A.sideCount (A.interiorCell j) = 2 := by simp only [sideCount, A.kind_interiorCell, if_true]

theorem EndpointArchitecture.sideTotal_pos (A : EndpointArchitecture) : 0 < A.sideTotal :=
  Finset.sum_pos' (fun i _ => (A.sideCount_pos i).le)
    ⟨⟨0, A.count_pos⟩, Finset.mem_univ _, A.sideCount_pos _⟩

theorem EndpointArchitecture.sideTotal_formula (A : EndpointArchitecture) :
    A.sideTotal = 2 * (A.interiorCount : ℝ) + A.leftReactive.toNat + A.rightReactive.toNat := by
  let f : Fin (A.interiorCount + 2) → ℝ :=
    Fin.cons (A.leftReactive.toNat : ℝ) (Fin.snoc (fun _ : Fin A.interiorCount => (2 : ℝ)) A.rightReactive.toNat)
  have he : ∀ i, f (A.activeNode i) = A.sideCount i := by
    intro i
    cases hi : A.kind i with
    | ordinary =>
      obtain ⟨j, rfl⟩ := A.ordinary_is_interiorCell i hi
      rw [A.activeNode_interior, A.sideCount_interior]
      simp [f, trapNode]
    | leftEndpoint =>
      rw [A.activeNode_left i hi]
      simp only [f, Fin.cons_zero, sideCount, hi, reduceCtorEq, if_false,
        ((A.kind_left_iff i).mp hi).1, Bool.toNat_true, Nat.cast_one]
    | rightEndpoint =>
      rw [A.activeNode_right i hi]
      simp [f, sideCount, hi, ((A.kind_right_iff i).mp hi).1]
  have hs := A.sum_active f (fun hl => by simp [f, hl]) (fun hr => by simp [f, hr])
  simp_rw [he] at hs
  change A.sideTotal = _ at hs
  rw [hs, Fin.sum_univ_succ]
  simp only [f, Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

noncomputable def EndpointArchitecture.homogeneousShare (A : EndpointArchitecture) (i : Fin A.count) : ℝ :=
  A.sideCount i / A.sideTotal

theorem EndpointArchitecture.homogeneousShare_pos (A : EndpointArchitecture) (i : Fin A.count) :
    0 < A.homogeneousShare i := div_pos (A.sideCount_pos i) A.sideTotal_pos

theorem EndpointArchitecture.homogeneousShare_sum (A : EndpointArchitecture) :
    (∑ i, A.homogeneousShare i) = 1 := by
  unfold homogeneousShare
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt A.sideTotal_pos)

noncomputable def EndpointArchitecture.homogeneousPartition (A : EndpointArchitecture) : StrictPartition A.count where
  point := absorptionPrefix A.homogeneousShare
  strictMono := absorptionPrefix_strictMono _ A.homogeneousShare_pos
  first := absorptionPrefix_zero _
  last := by rw [absorptionPrefix_last, A.homogeneousShare_sum]

theorem EndpointArchitecture.homogeneousPartition_width (A : EndpointArchitecture) (i : Fin A.count) :
    A.homogeneousPartition.closed.width i = A.homogeneousShare i := by
  change absorptionPrefix _ i.succ - absorptionPrefix _ i.castSucc = _
  rw [absorptionPrefix_succ, add_sub_cancel_left]

theorem EndpointArchitecture.barrier_constant (A : EndpointArchitecture) (Q : ClosedPartition A.count)
    (W : CellWeight) {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (i : Fin A.count) :
    A.barrier Q W i = C * Q.width i ^ 2 / (2 * A.sideCount i ^ 2) := by
  unfold barrier
  rw [W.orientedBarrier_constant _ hC (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))]
  cases hi : A.kind i <;> simp only [sideCount, hi, reduceCtorEq, if_true, if_false] <;>
    change _ = C * (Q.point i.succ - Q.point i.castSucc) ^ 2 / _ <;> norm_num

theorem EndpointArchitecture.cubic_width_bound (A : EndpointArchitecture) (Q : ClosedPartition A.count) :
    1 / A.sideTotal ^ 2 ≤ (∑ i, Q.width i ^ 3 / A.sideCount i ^ 2) ∧
      ((∑ i, Q.width i ^ 3 / A.sideCount i ^ 2) = 1 / A.sideTotal ^ 2 ↔
        ∀ i, Q.width i = A.homogeneousShare i) := by
  have h := cubic_length_bound Finset.univ A.sideCount Q.width A.sideTotal_pos
    (by norm_num : (0 : ℝ) < 1) rfl Q.width_sum (fun i _ => A.sideCount_pos i)
    (fun i _ => Q.width_nonneg i)
  simpa only [one_pow, one_mul, Finset.mem_univ, forall_const, homogeneousShare] using h

theorem EndpointArchitecture.homogeneousPartition_unique (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (hw : ∀ i, Q.width i = A.homogeneousShare i) :
    Q = A.homogeneousPartition.closed := by
  apply Subtype.ext
  funext e
  change Q.point e = A.homogeneousPartition.point e
  induction e using Fin.induction with
  | zero => rw [Q.first, A.homogeneousPartition.first]
  | succ i ih =>
    have hq := hw i
    have hp := A.homogeneousPartition_width i
    change Q.point i.succ - Q.point i.castSucc = _ at hq
    change A.homogeneousPartition.point i.succ - A.homogeneousPartition.point i.castSucc = _ at hp
    linarith

end TimeTraps.Interval
