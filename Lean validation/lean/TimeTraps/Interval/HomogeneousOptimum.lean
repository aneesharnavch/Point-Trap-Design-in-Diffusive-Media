module

public import TimeTraps.Interval.HomogeneousDesign
public import TimeTraps.Interval.GlobalOptimization

@[expose] public section

/-!
The homogeneous interval optimum for every admissible physical weak design:
L/K + L²/(8Dn²), attained exactly at equal-cell midpoints with strengths K/n.
The proof includes all competing ordered sites and positive allocations.
-/

namespace TimeTraps.Interval

open Set

variable {L D K : ℝ} {n : ℕ}

theorem homogeneous_lower_bound (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ≤ E.cost := by
  have h := E.partition.closed.constant_root_lower (homogeneous L D hL hD).cellWeight
    (fun z _ => homogeneous_weight hL hD z) (div_pos hK (homogeneous L D hL hD).source.mass_pos)
  rw [homogeneous_normalized_height hL hD hn hK] at h
  exact h.trans (E.partition_root_lower_bound hK)

/-- The explicitly displayed homogeneous value is an attained least cost
over the independent physical weak-design space. -/
theorem homogeneous_minimum (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    IsLeast (range (fun E : IntervalDesign (homogeneous L D hL hD) n K => E.cost))
      (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) := by
  refine ⟨⟨(homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK,
    homogeneous_construct_cost hL hD hn hK⟩, ?_⟩
  rintro M ⟨E, rfl⟩
  exact homogeneous_lower_bound hL hD hn hK E

theorem homogeneous_construct_optimal (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).Optimal := by
  apply IntervalMedium.construct_optimal
  exact ((StrictPartition.uniform n hn).constant_minimizer_iff _ hn
    (fun z _ => homogeneous_weight hL hD z) (div_pos hK (homogeneous L D hL hD).source.mass_pos)).mpr rfl

theorem homogeneous_optimal_partition (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) (hE : E.Optimal) :
    E.partition = StrictPartition.uniform n hn :=
  (E.partition.constant_minimizer_iff _ hn (fun z _ => homogeneous_weight hL hD z)
    (div_pos hK (homogeneous L D hL hD).source.mass_pos)).mp (E.optimal_partition hK hE)

/-- Complete uniqueness of both labeled physical parameter vectors. The
zero-based index i corresponds to the paper's one-based index i+1. -/
theorem homogeneous_optimal_iff (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.Optimal ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  constructor
  · intro hE
    have hQ := homogeneous_optimal_partition hL hD hn hK E hE
    have hp := E.optimal_parameters hK hE
    rw [hQ] at hp
    exact ⟨fun i => (hp i).1.trans (homogeneous_uniform_sites hL hD hn i),
      fun i => (hp i).2.trans (homogeneous_uniform_strength hL hD hn hK i)⟩
  · rintro ⟨hx, hκ⟩
    have hc : E.cost = ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).cost := by
      apply E.cost_eq_of_parameters
      · intro i
        exact (hx i).trans (homogeneous_construct_sites hL hD hn hK i).symm
      · exact funext (fun i => (hκ i).trans (homogeneous_construct_strength hL hD hn hK i).symm)
    intro F
    rw [hc]
    exact homogeneous_construct_optimal hL hD hn hK F

theorem homogeneous_cost_eq_iff (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.cost = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  have he : E.cost = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ↔ E.Optimal := by
    constructor
    · intro h F
      rw [h]
      exact homogeneous_lower_bound hL hD hn hK F
    · intro h
      apply le_antisymm
      · have hc := h ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK)
        rwa [homogeneous_construct_cost hL hD hn hK] at hc
      · exact homogeneous_lower_bound hL hD hn hK E
  exact he.trans (homogeneous_optimal_iff hL hD hn hK E)

theorem homogeneous_optimal_shares (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) (hE : E.Optimal) (i : Fin n) :
    E.geometry.stateShare E.strength E.state i = 1 / (n : ℝ) := by
  rw [← E.partition_width i, homogeneous_optimal_partition hL hD hn hK E hE]
  exact StrictPartition.uniform_width hn i

theorem homogeneous_optimal_trap_value (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) (hE : E.Optimal) (i : Fin n) :
    E.state (E.geometry.site i) = L / K := by
  have hcost := (homogeneous_cost_eq_iff hL hD hn hK E).mpr
    ((homogeneous_optimal_iff hL hD hn hK E).mp hE)
  have hR : E.geometry.stateBarrier E.strength E.state i = L ^ 2 / (8 * D * (n : ℝ) ^ 2) := by
    rw [← E.partition_barrier i, homogeneous_optimal_partition hL hD hn hK E hE]
    exact homogeneous_uniform_barrier hL hD hn i
  have hl := E.equation.budget_equality_loss E.strength_pos (E.optimal_budget_equality hK hE) i
  change E.cost - E.state (E.geometry.site i) = _ at hl
  rw [hcost, hR] at hl
  linarith

end TimeTraps.Interval
