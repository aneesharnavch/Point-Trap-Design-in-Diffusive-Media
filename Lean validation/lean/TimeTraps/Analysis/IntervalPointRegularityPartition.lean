module

public import TimeTraps.Analysis.IntervalPointRegularityLocal
public import TimeTraps.Analysis.IntervalPointRegularityNodeTest

@[expose] public section

/-! A strict ordered partition containing every physical contact. Multiple
contacts may occupy one node, and extra nodes may have zero total strength.
Endpoint contacts are retained explicitly. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

structure UnitPointPartition {ι : Type*} [Fintype ι] (P : UnitPointProblem ι) (n : ℕ) where
  point : Fin (n + 2) → ℝ
  strictMono : StrictMono point
  left_eq : point 0 = 0
  right_eq : point (Fin.last (n + 1)) = 1
  contactNode : ι → Fin (n + 2)
  contact_eq : ∀ i, P.site i = point (contactNode i)

noncomputable def UnitPointPartition.nodeStrength {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n) (v : Fin (n + 2)) : ℝ :=
  ∑ i, if Q.contactNode i = v then P.strength i else 0

theorem UnitPointPartition.nodeStrength_nonneg {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n) (v : Fin (n + 2)) :
    0 ≤ Q.nodeStrength v := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact P.strength_nonneg i
  · exact le_rfl

theorem UnitPointPartition.point_mem {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n) (v : Fin (n + 2)) :
    Q.point v ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← Q.left_eq]
    exact Q.strictMono.monotone (Fin.zero_le v)
  · rw [← Q.right_eq]
    exact Q.strictMono.monotone (Fin.le_last v)

theorem UnitPointPartition.no_contact_cell {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n) (e : Fin (n + 1)) (i : ι) :
    P.site i ∉ Ioo (Q.point e.castSucc) (Q.point e.succ) := by
  rw [Q.contact_eq]
  intro hi
  have hl := Q.strictMono.lt_iff_lt.mp hi.1
  have hr := Q.strictMono.lt_iff_lt.mp hi.2
  change (e : ℕ) < (Q.contactNode i : ℕ) at hl
  change (Q.contactNode i : ℕ) < (e : ℕ) + 1 at hr
  omega

theorem UnitPointPartition.local_slopes {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ 0 1 →
      unitPointForm P.diffusivity P.strength P.site u ψ = ∫ x in (0 : ℝ)..1, f x * ψ x) :
    ∃ v : Fin (n + 1) → ℝ → ℝ, ∀ e,
      IntervalSlopeRegularity u (v e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ) := by
  have he (e : Fin (n + 1)) := P.weak_local_regularity f hu hweak
    (Q.point_mem e.castSucc).1 (Q.strictMono Fin.castSucc_lt_succ)
    (Q.point_mem e.succ).2 (Q.no_contact_cell e)
  choose v hv using he
  exact ⟨v, hv⟩

theorem UnitPointPartition.nodeTest_reaction {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n)
    (u : ℝ → ℝ) (v : Fin (n + 2)) :
    (∑ i, P.strength i * u (P.site i) * intervalNodeTest Q.point v (P.site i)) =
      Q.nodeStrength v * u (Q.point v) := by
  classical
  unfold nodeStrength
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Q.contact_eq, intervalNodeTest_node Q.point Q.strictMono.injective]
  by_cases hi : Q.contactNode i = v
  · simp [hi]
  · simp only [if_neg hi, mul_zero, zero_mul]

end TimeTraps.Analysis
