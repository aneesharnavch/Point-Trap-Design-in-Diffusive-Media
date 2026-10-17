module

public import TimeTraps.Analysis.RegularSturmPositiveGroundPropagation

@[expose] public section

/-! A nonnegative regular Sturm eigenstate cannot vanish at an interior
point unless it is zero. At contact nodes the two inward flux signs and
the literal zero jump supply zero Cauchy data. Signed potentials and
contact strengths and variable continuous conductance/speed are retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}
variable {P : RegularSturmProblem ι l r} {n : ℕ}

theorem RegularSturmPartition.interior_zero_fluxes
    (Q : RegularSturmPartition P n) {u c : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    (hj : ∀ e, IntervalFluxRegularity u (j e) (fun x => c x * u x) P.conductance
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : RegularSturmTransmission Q u j)
    (hn : ∀ x ∈ Icc l r, 0 ≤ u x) (i : Fin n) (hz : u (Q.point i.castSucc.succ) = 0) :
    j i.castSucc (Q.point i.castSucc.succ) = 0 ∧ j i.succ (Q.point i.castSucc.succ) = 0 := by
  have hs (e : Fin (n + 1)) : Icc (Q.point e.castSucc) (Q.point e.succ) ⊆ Icc l r :=
    Icc_subset_Icc (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2
  have hl := (hj i.castSucc).right_flux_nonpos_of_nonnegative_zero
    (Q.strictMono Fin.castSucc_lt_succ) (P.conductance_continuous.mono (hs i.castSucc))
    (fun x hx => P.conductance_pos x (hs i.castSucc hx)) (fun x hx => hn x (hs i.castSucc hx)) hz
  have hz' : u (Q.point i.succ.castSucc) = 0 := by simpa only [Fin.succ_castSucc] using hz
  have hr := (hj i.succ).left_flux_nonneg_of_nonnegative_zero
    (Q.strictMono Fin.castSucc_lt_succ) (P.conductance_continuous.mono (hs i.succ))
    (fun x hx => P.conductance_pos x (hs i.succ hx)) (fun x hx => hn x (hs i.succ hx)) hz'
  rw [← Fin.succ_castSucc] at hr
  have he := ht.interior_jump i
  rw [hz, mul_zero] at he
  constructor <;> linarith

theorem RegularSturmPartition.eq_zero_of_nonnegative_interior_zero
    (Q : RegularSturmPartition P n) {u c : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    (hc : ContinuousOn c (Icc l r))
    (hj : ∀ e, IntervalFluxRegularity u (j e) (fun x => c x * u x) P.conductance
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : RegularSturmTransmission Q u j)
    (hn : ∀ x ∈ Icc l r, 0 ≤ u x) {x : ℝ} (hx : x ∈ Ioo l r) (hz : u x = 0) :
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
        have hsj := Q.interior_zero_fluxes hj ht hn i hzero
        exact ⟨i.castSucc, Q.cell_eq_zero_of_linear_cauchy hc (hj i.castSucc)
          (Q.strictMono Fin.castSucc_lt_succ).le
          ⟨(Q.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩ hzero hsj.1⟩
  have hseed : ∃ e, C e := by
    by_cases hnodeAt : ∃ v, Q.point v = x
    · obtain ⟨v, rfl⟩ := hnodeAt
      exact hnode v hx hz
    · obtain ⟨e, he⟩ := Q.gap_cover (Ioo_subset_Icc_self hx)
      have hi : x ∈ Ioo (Q.point e.castSucc) (Q.point e.succ) := by
        constructor
        · exact lt_of_le_of_ne he.1 (fun h => hnodeAt ⟨e.castSucc, h⟩)
        · exact lt_of_le_of_ne he.2 (fun h => hnodeAt ⟨e.succ, h.symm⟩)
      have hs : Icc (Q.point e.castSucc) (Q.point e.succ) ⊆ Icc l r :=
        Icc_subset_Icc (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2
      have hjz := (hj e).flux_zero_of_nonnegative_interior_zero (P.conductance_continuous.mono hs)
        (fun y hy => P.conductance_pos y (hs hy)) (fun y hy => hn y (hs hy)) hi hz
      exact ⟨e, Q.cell_eq_zero_of_linear_cauchy hc (hj e)
        (Q.strictMono Fin.castSucc_lt_succ).le he hz hjz⟩
  obtain ⟨e, he⟩ := hseed
  have hall := Q.all_cells_zero_of_cell_zero hc hj ht e he
  intro y hy
  obtain ⟨d, hd⟩ := Q.gap_cover hy
  exact (hall d y hd).1

end TimeTraps.Analysis
