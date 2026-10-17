module

public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundPropagation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! An interior zero of a nonnegative state forces zero Cauchy data on a cell.
Zero propagation then excludes every interior zero of a nontrivial state.
Endpoint zeros are treated separately using the periodic seam law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}
variable {P : SignedPeriodicPointProblem ι l r} {n : ℕ}

theorem SignedPeriodicPointPartition.interior_zero_slopes
    (Q : SignedPeriodicPointPartition P n) {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    {c : ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => c * u x)
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : SignedPeriodicPointTransmission Q u j)
    (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u x) (i : Fin n)
    (hz : u (Q.point i.castSucc.succ) = 0) :
    j i.castSucc (Q.point i.castSucc.succ) = 0 ∧ j i.succ (Q.point i.castSucc.succ) = 0 := by
  have hc (e : Fin (n + 1)) : ContinuousOn (j e) (Icc (Q.point e.castSucc) (Q.point e.succ)) := by
    simpa only [uIcc_of_le (Q.strictMono Fin.castSucc_lt_succ).le] using (hj e).slope_energy.continuousOn
  have hl := intervalEnergy_hasDerivWithinAt_right_of_ae_deriv (hj i.castSucc).state_energy
    (Q.strictMono Fin.castSucc_lt_succ) (hc i.castSucc) (hj i.castSucc).slope_ae
  have hr := intervalEnergy_hasDerivWithinAt_left_of_ae_deriv (hj i.succ).state_energy
    (Q.strictMono Fin.castSucc_lt_succ) (hc i.succ) (hj i.succ).slope_ae
  rw [← Fin.succ_castSucc] at hr
  have hmatch : j i.succ (Q.point i.castSucc.succ) = j i.castSucc (Q.point i.castSucc.succ) := by
    have he := ht.interior_jump i
    rw [hz, mul_zero] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne')
  rw [hmatch] at hr
  have hd : HasDerivAt u (j i.castSucc (Q.point i.castSucc.succ)) (Q.point i.castSucc.succ) := by
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  have hx : Q.point i.castSucc.succ ∈ Ioo l r := by
    constructor
    · exact Q.left_eq.symm.trans_lt (Q.strictMono (Fin.succ_pos _))
    · apply (Q.strictMono _).trans_eq Q.right_eq
      simpa only [Fin.succ_castSucc] using Fin.castSucc_lt_last i.succ
  have hmin : IsLocalMin u (Q.point i.castSucc.succ) := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with x hx'
    rw [hz]
    exact hnonneg x hx'
  have hzero := hmin.hasDerivAt_eq_zero hd
  exact ⟨hzero, hmatch.trans hzero⟩

theorem SignedPeriodicPointPartition.eq_zero_of_nonnegative_interior_zero
    (Q : SignedPeriodicPointPartition P n) {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    {c : ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => c * u x)
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : SignedPeriodicPointTransmission Q u j)
    (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u x) {x : ℝ} (hx : x ∈ Ioo l r) (hz : u x = 0) :
    ∀ y ∈ Icc l r, u y = 0 := by
  let C : Fin (n + 1) → Prop := fun e =>
    ∀ y ∈ Icc (Q.point e.castSucc) (Q.point e.succ), u y = 0 ∧ j e y = 0
  have hnode : ∀ v : Fin (n + 2), Q.point v ∈ Ioo l r → u (Q.point v) = 0 → ∃ e, C e := by
    intro v
    refine Fin.cases ?_ (fun w => ?_) v
    · intro hv _
      have he := hv.1
      rw [Q.left_eq] at he
      exact (lt_irrefl _ he).elim
    · refine Fin.lastCases ?_ (fun i => ?_) w
      · intro hv _
        have he := hv.2
        rw [Fin.succ_last, Q.right_eq] at he
        exact (lt_irrefl _ he).elim
      · intro _ hzero
        have hsj := Q.interior_zero_slopes hj ht hnonneg i hzero
        exact ⟨i.castSucc, (hj i.castSucc).eq_zero_of_linear_cauchy
          (Q.strictMono Fin.castSucc_lt_succ)
          ⟨(Q.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩ hzero hsj.1⟩
  have hseed : ∃ e, C e := by
    by_cases hn : ∃ v, Q.point v = x
    · obtain ⟨v, rfl⟩ := hn
      exact hnode v hx hz
    · obtain ⟨e, he⟩ := Q.gap_cover (Ioo_subset_Icc_self hx)
      have hi : x ∈ Ioo (Q.point e.castSucc) (Q.point e.succ) := by
        constructor
        · exact lt_of_le_of_ne he.1 (fun h => hn ⟨e.castSucc, h⟩)
        · exact lt_of_le_of_ne he.2 (fun h => hn ⟨e.succ, h.symm⟩)
      have hmin : IsLocalMin u x := by
        filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
        rw [hz]
        exact hnonneg y hy
      have hsj := hmin.hasDerivAt_eq_zero ((hj e).hasDerivAt hi)
      exact ⟨e, (hj e).eq_zero_of_linear_cauchy (Q.strictMono Fin.castSucc_lt_succ) he hz hsj⟩
  obtain ⟨e, he⟩ := hseed
  have hall := Q.all_cells_zero_of_cell_zero hj ht e he
  intro y hy
  obtain ⟨d, hd⟩ := Q.gap_cover hy
  exact (hall d y hd).1

end TimeTraps.Analysis
