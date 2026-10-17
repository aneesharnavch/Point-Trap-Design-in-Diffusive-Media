module

public import TimeTraps.Interval.VariableMeanEnergy
public import TimeTraps.Interval.WeightedGridCells

@[expose] public section

/-! The actual sites and strengths prescribed by a strict weighted grid.
Geometry and the budget are defined before any state or attainment claim. -/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

theorem StrictPartition.canonicalMidpoint_strictMono (Q : StrictPartition n) :
    StrictMono Q.closed.canonicalMidpoint := by
  intro i j hij
  have h1 := Q.strictMono (Fin.castSucc_lt_castSucc_iff.mpr hij)
  have h2 := Q.strictMono (Fin.succ_lt_succ_iff.mpr hij)
  change (Q.point i.castSucc + Q.point i.succ) / 2 <
    (Q.point j.castSucc + Q.point j.succ) / 2
  linarith

theorem StrictPartition.canonicalMidpoint_interior (Q : StrictPartition n) (i : Fin n) :
    Q.closed.canonicalMidpoint i ∈ Ioo (0 : ℝ) 1 := by
  have hl := Q.point_mem i.castSucc
  have hr := Q.point_mem i.succ
  have hi := Q.strictMono (Fin.castSucc_lt_succ (i := i))
  change (Q.point i.castSucc + Q.point i.succ) / 2 ∈ Ioo (0 : ℝ) 1
  constructor <;> linarith [hl.1, hr.2]

noncomputable def variableGridGeometry (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) : OrderedMedium n :=
  OrderedMedium.ofSites (variableUnitMedium a ha hapos).source a ha hapos
    Q.closed.canonicalMidpoint Q.canonicalMidpoint_strictMono Q.canonicalMidpoint_interior

theorem variableGridGeometry_site (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (i : Fin n) :
    (variableGridGeometry Q a ha hapos).site i = Q.closed.canonicalMidpoint i := by
  exact OrderedMedium.ofSites_site _ _ _ _ _ _ _ i

theorem variableGridGeometry_node (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (v : Fin (n + 2)) :
    (variableGridGeometry Q a ha hapos).node v = Q.closed.canonicalCellNode v := rfl

noncomputable def variableGridStrength (Q : StrictPartition n) (K : ℝ) (i : Fin n) : ℝ :=
  K * Q.width i

theorem variableGridStrength_pos (Q : StrictPartition n) {K : ℝ} (hK : 0 < K) (i : Fin n) :
    0 < variableGridStrength Q K i := mul_pos hK (Q.width_pos i)

theorem variableGridStrength_sum (Q : StrictPartition n) (K : ℝ) :
    ∑ i, variableGridStrength Q K i = K := by
  simp only [variableGridStrength, ← Finset.mul_sum, Q.width_sum, mul_one]

theorem variableGridStrength_reaction (Q : StrictPartition n) {K : ℝ} (hK : K ≠ 0)
    (i : Fin n) : variableGridStrength Q K i * (1 / K) = Q.width i := by
  unfold variableGridStrength
  field_simp

end TimeTraps.Interval
