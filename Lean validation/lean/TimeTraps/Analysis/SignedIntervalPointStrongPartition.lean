module

public import TimeTraps.Analysis.SignedIntervalPointStrongLocal
public import TimeTraps.Analysis.GeneralIntervalPointRegularityPartition

@[expose] public section

/-! A strict ordered partition containing every real-strength physical contact. Multiple
contacts may occupy one node, and extra nodes may have zero total strength.
Endpoint contacts are retained explicitly. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

structure SignedIntervalPointPartition {ι : Type*} [Fintype ι] (P : SignedIntervalPointProblem ι l r) (n : ℕ) where
  point : Fin (n + 2) → ℝ
  strictMono : StrictMono point
  left_eq : point 0 = l
  right_eq : point (Fin.last (n + 1)) = r
  contactNode : ι → Fin (n + 2)
  contact_eq : ∀ i, P.site i = point (contactNode i)

noncomputable def SignedIntervalPointPartition.nodeStrength {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n) (v : Fin (n + 2)) : ℝ :=
  ∑ i, if Q.contactNode i = v then P.strength i else 0

theorem SignedIntervalPointPartition.point_mem {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n) (v : Fin (n + 2)) :
    Q.point v ∈ Icc l r := by
  constructor
  · exact Q.left_eq.symm.trans_le (Q.strictMono.monotone (Fin.zero_le v))
  · exact (Q.strictMono.monotone (Fin.le_last v)).trans_eq Q.right_eq

theorem SignedIntervalPointPartition.no_contact_cell {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n) (e : Fin (n + 1)) (i : ι) :
    P.site i ∉ Ioo (Q.point e.castSucc) (Q.point e.succ) := by
  rw [Q.contact_eq]
  intro hi
  have hl := Q.strictMono.lt_iff_lt.mp hi.1
  have hr := Q.strictMono.lt_iff_lt.mp hi.2
  change (e : ℕ) < (Q.contactNode i : ℕ) at hl
  change (Q.contactNode i : ℕ) < (e : ℕ) + 1 at hr
  omega

theorem SignedIntervalPointPartition.local_slopes {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x) :
    ∃ v : Fin (n + 1) → ℝ → ℝ, ∀ e,
      IntervalSlopeRegularity u (v e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ) := by
  have he (e : Fin (n + 1)) := P.weak_local_regularity f hu hweak
    (Q.point_mem e.castSucc).1 (Q.strictMono Fin.castSucc_lt_succ)
    (Q.point_mem e.succ).2 (Q.no_contact_cell e)
  choose v hv using he
  exact ⟨v, hv⟩

theorem SignedIntervalPointPartition.nodeTest_reaction {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n)
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

theorem SignedIntervalPointPartition.energy_of_piecewise {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n) {u : ℝ → ℝ}
    (hu : ∀ e : Fin (n + 1), IntervalEnergy u (Q.point e.castSucc) (Q.point e.succ)) :
    IntervalEnergy u l r := by
  simpa only [Q.left_eq, Q.right_eq] using
    intervalEnergy_of_finite_chain Q.point Q.strictMono.monotone hu

theorem SignedIntervalPointPartition.energy_of_slopes {ι : Type*} [Fintype ι]
    {P : SignedIntervalPointProblem ι l r} {n : ℕ} (Q : SignedIntervalPointPartition P n)
    {u g : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) g (Q.point e.castSucc) (Q.point e.succ)) :
    IntervalEnergy u l r := Q.energy_of_piecewise (fun e => (hj e).state_energy)

end TimeTraps.Analysis
