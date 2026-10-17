module

public import TimeTraps.Analysis.VertexSystem

@[expose] public section

/-!
Finite edge incidence with separate tail and head contributions. Edges have
their own identifiers, so parallel edges remain distinct and a loop contributes
at both ends. Connectivity is a property of incidence, not of a solution.
-/

namespace TimeTraps.Graph

open scoped BigOperators
open TimeTraps.Analysis

variable {V E : Type*} [Fintype E]

noncomputable def incidenceWeight (tail head : E → V) (c : E → ℝ) (v w : V) : ℝ := by
  classical
  exact ∑ e, ((if tail e = v ∧ head e = w then c e else 0) +
    (if head e = v ∧ tail e = w then c e else 0))

noncomputable def incidenceLoad (tail head : E → V) (p q : E → ℝ) (v : V) : ℝ := by
  classical
  exact ∑ e, ((if tail e = v then p e else 0) + (if head e = v then q e else 0))

/-- Sum of derivatives directed from the vertex into its incident edges. -/
noncomputable def vertexFlux (tail head : E → V) (j₀ j₁ : E → ℝ) : V → ℝ :=
  incidenceLoad tail head j₀ (fun e => -j₁ e)

def IncidenceConnected (tail head : E → V) : Prop :=
  ∀ v w, Relation.EqvGen (fun v w => ∃ e, tail e = v ∧ head e = w) v w

theorem incidenceWeight_symmetric (tail head : E → V) (c : E → ℝ) (v w : V) :
    incidenceWeight tail head c v w = incidenceWeight tail head c w v := by
  classical
  unfold incidenceWeight
  apply Finset.sum_congr rfl
  intro e _
  simp only [and_comm]
  ring

theorem incidenceWeight_nonneg (tail head : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (v w : V) : 0 ≤ incidenceWeight tail head c v w := by
  classical
  apply Finset.sum_nonneg
  intro e _
  exact add_nonneg (by split_ifs <;> simp_all) (by split_ifs <;> simp_all)

theorem incidenceWeight_edge_pos (tail head : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) (e : E) : 0 < incidenceWeight tail head c (tail e) (head e) := by
  classical
  apply Finset.sum_pos'
  · intro d _
    exact add_nonneg (by split_ifs <;> simp_all [le_of_lt])
      (by split_ifs <;> simp_all [le_of_lt])
  · refine ⟨e, Finset.mem_univ e, ?_⟩
    simp only [true_and, ite_true]
    split_ifs <;> linarith [hc e]

theorem incidence_connected_weights (tail head : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) (hconn : IncidenceConnected tail head) :
    ∀ v w, Relation.EqvGen (fun v w => 0 < incidenceWeight tail head c v w) v w := by
  intro v w
  induction hconn v w with
  | rel v w hvw =>
      obtain ⟨e, rfl, rfl⟩ := hvw
      exact Relation.EqvGen.rel _ _ (incidenceWeight_edge_pos tail head c hc e)
  | refl v => exact Relation.EqvGen.refl v
  | symm v w _ ih => exact Relation.EqvGen.symm v w ih
  | trans v w z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans v w z ih₁ ih₂

omit [Fintype E] in
/-- A nonempty connected edge set leaves no isolated vertex. -/
theorem connected_vertex_incident [Nonempty E] (tail head : E → V)
    (hconn : IncidenceConnected tail head) (v : V) :
    ∃ e, tail e = v ∨ head e = v := by
  let e₀ : E := Classical.choice inferInstance
  have hequiv : ∀ x y, Relation.EqvGen (fun x y => ∃ e, tail e = x ∧ head e = y) x y →
      ((∃ e, tail e = x ∨ head e = x) ↔ (∃ e, tail e = y ∨ head e = y)) := by
    intro x y hxy
    induction hxy with
    | rel x y h =>
        obtain ⟨e, ht, hh⟩ := h
        exact ⟨fun _ => ⟨e, Or.inr hh⟩, fun _ => ⟨e, Or.inl ht⟩⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hequiv (tail e₀) v (hconn _ _)).mp ⟨e₀, Or.inl rfl⟩

theorem incidenceLoad_pos [Nonempty E] (tail head : E → V) (p q : E → ℝ)
    (hp : ∀ e, 0 < p e) (hq : ∀ e, 0 < q e)
    (hconn : IncidenceConnected tail head) (v : V) :
    0 < incidenceLoad tail head p q v := by
  classical
  obtain ⟨e, he⟩ := connected_vertex_incident tail head hconn v
  apply Finset.sum_pos'
  · intro d _
    exact add_nonneg (by split_ifs <;> simp_all [le_of_lt])
      (by split_ifs <;> simp_all [le_of_lt])
  · refine ⟨e, Finset.mem_univ e, ?_⟩
    rcases he with ht | hh
    · simp only [ht, ite_true]
      split_ifs <;> linarith [hp e, hq e]
    · simp only [hh, ite_true]
      split_ifs <;> linarith [hp e, hq e]

theorem incidenceLoad_sum [Fintype V] (tail head : E → V) (p q : E → ℝ) :
    ∑ v, incidenceLoad tail head p q v = ∑ e, (p e + q e) := by
  classical
  unfold incidenceLoad
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib]

/-- Reindexing the Laplacian counts each edge end, including both ends of loops. -/
theorem incidence_laplacian [Fintype V] (tail head : E → V) (c : E → ℝ) (x : V → ℝ) (v : V) :
    ∑ w, incidenceWeight tail head c v w * (x v - x w) =
      incidenceLoad tail head (fun e => c e * (x (tail e) - x (head e)))
        (fun e => c e * (x (head e) - x (tail e))) v := by
  classical
  unfold incidenceWeight incidenceLoad
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : tail e = v <;> by_cases hh : head e = v <;>
    simp [ht, hh, add_mul, Finset.sum_add_distrib]

theorem incidence_flux_balance [Fintype V] (tail head : E → V) (c p q : E → ℝ)
    (κ x : V → ℝ) (v : V) :
    (κ v * x v = vertexFlux tail head
      (fun e => c e * (x (head e) - x (tail e)) + p e)
      (fun e => c e * (x (head e) - x (tail e)) - q e) v) ↔
    vertexOperator (incidenceWeight tail head c) κ x v = incidenceLoad tail head p q v := by
  classical
  rw [vertexOperator_apply, incidence_laplacian]
  have heq : vertexFlux tail head
      (fun e => c e * (x (head e) - x (tail e)) + p e)
      (fun e => c e * (x (head e) - x (tail e)) - q e) v =
      incidenceLoad tail head p q v -
      incidenceLoad tail head (fun e => c e * (x (tail e) - x (head e)))
        (fun e => c e * (x (head e) - x (tail e))) v := by
    unfold vertexFlux incidenceLoad
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  rw [heq]
  exact eq_sub_iff_add_eq

/-- Endpoint products in Green's identity collect to minus the vertex flux. -/
theorem incidence_boundary_sum [Fintype V] (tail head : E → V) (j₀ j₁ : E → ℝ) (ψ : V → ℝ) :
    (∑ e, (j₁ e * ψ (head e) - j₀ e * ψ (tail e))) =
      -(∑ v, ψ v * vertexFlux tail head j₀ j₁ v) := by
  classical
  unfold vertexFlux incidenceLoad
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_add, Finset.sum_add_distrib, mul_ite, mul_comm, sub_eq_add_neg]

end TimeTraps.Graph
