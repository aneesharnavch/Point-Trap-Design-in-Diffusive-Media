module

public import TimeTraps.Interval.PartitionAttainment
public import TimeTraps.Interval.DesignEquality
public import TimeTraps.Interval.PartitionRoot

@[expose] public section

/-!
An independent admissible physical design at fixed medium, count and budget.
The state is required to satisfy the original weak equation. Its cost is
the physical essential norm; no balanced profile or optimality is assumed.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

theorem OrderedMedium.eq_of_medium_sites {D E : OrderedMedium n}
    (hmedium : D.medium = E.medium) (hsite : ∀ i, D.site i = E.site i) : D = E := by
  have hs : D.source = E.source := congrArg IntervalMedium.source hmedium
  have ha : D.conductance = E.conductance := congrArg IntervalMedium.conductance hmedium
  have hn : D.node = E.node := by
    funext v
    refine Fin.cases ?_ (fun k => ?_) v
    · rw [D.node_first, E.node_first, hs]
    · refine Fin.lastCases ?_ (fun i => ?_) k
      · change D.node (Fin.last (n + 1)) = E.node (Fin.last (n + 1))
        rw [D.node_last, E.node_last, hs]
      · exact hsite i
  cases D
  cases E
  dsimp only at hs ha hn
  cases hs
  cases ha
  cases hn
  rfl

theorem OrderedMedium.essentialNorm_congr (D : OrderedMedium n) {u v : ℝ → ℝ}
    (h : EqOn u v (Icc D.source.left D.source.right)) : D.essentialNorm u = D.essentialNorm v := by
  apply essSup_congr_ae
  exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx => congrArg abs (h hx))

structure IntervalDesign (A : IntervalMedium) (n : ℕ) (K : ℝ) where
  geometry : OrderedMedium n
  medium_eq : geometry.medium = A
  strength : Fin n → ℝ
  strength_pos : ∀ i, 0 < strength i
  strength_sum : (∑ i, strength i) = K
  state : ℝ → ℝ
  equation : WeakIntervalEquation geometry strength state

variable {A : IntervalMedium} {K : ℝ}

noncomputable def IntervalDesign.cost (D : IntervalDesign A n K) : ℝ :=
  D.geometry.essentialNorm D.state

noncomputable def IntervalDesign.partition (D : IntervalDesign A n K) : StrictPartition n :=
  D.equation.partition D.strength_pos

theorem IntervalDesign.source_mass (D : IntervalDesign A n K) : D.geometry.source.mass = A.source.mass :=
  congrArg (fun B : IntervalMedium => B.source.mass) D.medium_eq

theorem IntervalDesign.cellWeight_eq (D : IntervalDesign A n K) : D.geometry.medium.cellWeight = A.cellWeight :=
  congrArg IntervalMedium.cellWeight D.medium_eq

theorem IntervalDesign.partition_width (D : IntervalDesign A n K) (i : Fin n) :
    D.partition.closed.width i = D.geometry.stateShare D.strength D.state i :=
  D.equation.partition_width D.strength_pos i

theorem IntervalDesign.partition_barrier (D : IntervalDesign A n K) (i : Fin n) :
    D.partition.closed.barrier A.cellWeight i = D.geometry.stateBarrier D.strength D.state i := by
  rw [← D.cellWeight_eq]
  exact D.equation.partition_barrier D.strength_pos i

theorem IntervalDesign.partition_root_lower_bound (D : IntervalDesign A n K) (hK : 0 < K) :
    D.partition.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤ D.cost := by
  have ht := (D.partition.closed.root_spec A.cellWeight (div_pos hK A.source.mass_pos)).2
  rw [funext D.partition_width, funext D.partition_barrier] at ht
  apply D.equation.partition_root_lower_bound D.strength_pos D.partition.size_pos
  rw [D.strength_sum, D.source_mass]
  exact ht

noncomputable def IntervalMedium.construct (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K) : IntervalDesign A n K where
  geometry := A.partitionDesign Q
  medium_eq := rfl
  strength := A.partitionStrength Q (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos))
  strength_pos := A.partitionStrength_pos Q (Q.closed.root_spec A.cellWeight (div_pos hK A.source.mass_pos)).1
  strength_sum := A.partition_strength_budget Q (Q.closed.root_spec A.cellWeight (div_pos hK A.source.mass_pos)).2
  state := A.partitionState Q (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos))
  equation := A.partition_weak_equation Q (Q.closed.root_spec A.cellWeight (div_pos hK A.source.mass_pos)).1

theorem IntervalMedium.construct_cost (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K) :
    (A.construct Q hK).cost = Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos) :=
  A.partition_norm Q (Q.closed.root_spec A.cellWeight (div_pos hK A.source.mass_pos)).1

theorem IntervalMedium.construct_sites (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K) (i : Fin n) :
    (A.construct Q hK).geometry.site i = A.partitionSites Q i :=
  A.partitionDesign_site Q i

theorem IntervalMedium.construct_strength (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K) (i : Fin n) :
    (A.construct Q hK).strength i =
      A.partitionStrength Q (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) i := rfl

/-- Weak uniqueness makes the objective independent of the chosen state
representative, and of the record used for the same physical sites. -/
theorem IntervalDesign.cost_eq_of_parameters (D E : IntervalDesign A n K)
    (hsite : ∀ i, D.geometry.site i = E.geometry.site i) (hκ : D.strength = E.strength) :
    D.cost = E.cost := by
  have hG := OrderedMedium.eq_of_medium_sites (D.medium_eq.trans E.medium_eq.symm) hsite
  have hw := D.equation
  rw [hG, hκ] at hw
  have he := interval_weak_state_unique hw E.equation (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos ⟨0, E.partition.size_pos⟩⟩
  change D.geometry.essentialNorm D.state = E.geometry.essentialNorm E.state
  rw [hG]
  exact E.geometry.essentialNorm_congr he

end TimeTraps.Interval
