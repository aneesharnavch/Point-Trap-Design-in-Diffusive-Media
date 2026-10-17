module

public import TimeTraps.Interval.SourceMeanCDF
public import TimeTraps.Interval.SourceMeanDeficit

@[expose] public section

/-!
Analytic specialization to a positive continuous unit stationary density.
The objective is the physical density-weighted integral. The effective
resistance is 1/(a(X) π(X)), and all three displayed losses retain their
physical strength and inverse-coordinate position interpretation. Stochastic
identification and construction of an attaining design are separate claims.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

def reversibleUnitMedium (a π : ℝ → ℝ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (hπ : ContinuousOn π (Icc (0 : ℝ) 1))
    (hπpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < π x) : IntervalMedium where
  source := ⟨0, 1, zero_lt_one, π, hπ, hπpos⟩
  conductance := a
  conductance_continuous := ha
  conductance_pos := hapos

noncomputable def reversibleMeanCost (π u : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, π x * u x

variable {n : ℕ} {K : ℝ} {a π : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)} {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}
  {hπ : ContinuousOn π (Icc (0 : ℝ) 1)} {hπpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < π x}

theorem reversibleUnitMedium_mass (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1) :
    (reversibleUnitMedium a π ha hapos hπ hπpos).source.mass = 1 := hπmass

theorem reversibleUnitMedium_coordinate (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1) (x : ℝ) :
    (reversibleUnitMedium a π ha hapos hπ hπpos).source.coordinate x = ∫ t in (0 : ℝ)..x, π t := by
  change (∫ t in (0 : ℝ)..x, π t) / (∫ t in (0 : ℝ)..1, π t) = _
  rw [hπmass, div_one]

theorem reversibleUnitMedium_weight (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1) (z : ℝ) :
    (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight.value z =
      1 / (a ((reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse z) *
        π ((reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse z)) := by
  change (reversibleUnitMedium a π ha hapos hπ hπpos).source.mass ^ 2 / _ = _
  rw [reversibleUnitMedium_mass hπmass, one_pow]
  rfl

theorem reversible_mean_objective (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) :
    E.sourceMeanCost = reversibleMeanCost π E.state := by
  change (∫ x in (0 : ℝ)..1, π x * E.state x) /
    (reversibleUnitMedium a π ha hapos hπ hπpos).source.mass = _
  rw [reversibleUnitMedium_mass hπmass, div_one]
  rfl

theorem reversible_mean_transformed (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) :
    reversibleMeanCost π E.state = ∫ z in (0 : ℝ)..1,
      E.state ((reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse z) := by
  rw [← reversible_mean_objective hπmass E]
  exact E.sourceMeanCost_transformed

theorem reversible_mean_cdf_energy (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) :
    reversibleMeanCost π E.state = (∑ i, E.partition.width i ^ 2 / E.strength i) +
      ∫ z in (0 : ℝ)..1,
        (1 / (a ((reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse z) *
          π ((reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse z))) *
            (E.geometry.absorptionCDF E.partition.width z - z) ^ 2 := by
  have he := source_mean_cdf_integral E
  simp_rw [reversibleUnitMedium_weight hπmass] at he
  rw [reversible_mean_objective hπmass E, reversibleUnitMedium_mass hπmass, one_mul] at he
  exact he

theorem reversible_mean_grid_deficit (hK : 0 < K) (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) (Q : ClosedPartition n) :
    reversibleMeanCost π E.state -
      (1 / K + Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) =
      meanStrengthLoss K E.strength E.partition.width +
      2 * (∑ i : Fin n, E.partition.width i *
        ∫ t in min (E.geometry.sourceSite i) (weightedCDFMidpoint E.partition.width i)..
          max (E.geometry.sourceSite i) (weightedCDFMidpoint E.partition.width i),
          (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight.value t *
            |t - weightedCDFMidpoint E.partition.width i|) +
      (E.partition.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight -
        Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) := by
  have he := source_mean_grid_deficit hK E Q
  simp_rw [source_mean_oriented_abs] at he
  simpa only [reversible_mean_objective hπmass E, reversibleUnitMedium_mass hπmass, one_mul] using he

theorem reversible_mean_grid_lower_bound (hK : 0 < K) (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) (Q : ClosedPartition n)
    (hmin : ∀ P : ClosedPartition n,
      Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ≤
        P.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) :
    1 / K + Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ≤
      reversibleMeanCost π E.state := by
  simpa only [reversible_mean_objective hπmass E, reversibleUnitMedium_mass hπmass] using
    source_mean_grid_lower_bound hK E Q hmin

theorem reversible_mean_grid_eq_iff (hK : 0 < K) (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) (Q : ClosedPartition n)
    (hmin : ∀ P : ClosedPartition n,
      Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ≤
        P.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) :
    reversibleMeanCost π E.state = 1 / K + Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ↔
      (∀ i, E.strength i = K * E.partition.width i) ∧
      (∀ i, E.geometry.site i = (reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse
        (weightedCDFMidpoint E.partition.width i)) ∧
      E.partition.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight =
        Q.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight := by
  have he := source_mean_grid_eq_iff hK E Q hmin
  rw [reversible_mean_objective hπmass E, reversibleUnitMedium_mass hπmass] at he
  have hstrength : (∀ i, E.partition.width i = E.strength i / K) ↔
      ∀ i, E.strength i = K * E.partition.width i := by
    constructor
    · intro h i
      have hi := (eq_div_iff (ne_of_gt hK)).mp (h i)
      nlinarith
    · intro h i
      rw [h i]
      field_simp [ne_of_gt hK]
  rwa [hstrength] at he

end TimeTraps.Interval
