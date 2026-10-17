module

public import TimeTraps.Interval.WeightedCDFPosition
public import TimeTraps.Interval.HomogeneousMeanDeficit

@[expose] public section

/-!
The actual Lebesgue mean of a unit-source weak design with positive continuous
variable conductance. Self-testing the full H1 equation and the derived gap
flux identify its energy with the exact weighted CDF score.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

def variableUnitMedium (a : ℝ → ℝ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) : IntervalMedium where
  source := (homogeneous 1 1 zero_lt_one zero_lt_one).source
  conductance := a
  conductance_continuous := ha
  conductance_pos := hapos

noncomputable def variableMeanWeight (a : ℝ → ℝ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) : CellWeight where
  value := fun z => 1 / a z
  continuous := continuousOn_const.div ha (fun z hz => ne_of_gt (hapos z hz))
  positive := fun z hz => one_div_pos.mpr (hapos z hz)

variable {n : ℕ} {K : ℝ} {a : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)} {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}

theorem variableUnitMedium_mass : (variableUnitMedium a ha hapos).source.mass = 1 :=
  homogeneous_mass zero_lt_one zero_lt_one

theorem variableUnitMedium_coordinate (x : ℝ) :
    (variableUnitMedium a ha hapos).source.coordinate x = x := by
  change (homogeneous 1 1 zero_lt_one zero_lt_one).source.coordinate x = x
  rw [homogeneous_coordinate, div_one]

theorem IntervalDesign.variable_source (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    E.geometry.source = (variableUnitMedium a ha hapos).source :=
  congrArg IntervalMedium.source E.medium_eq

theorem IntervalDesign.variable_conductance (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    E.geometry.conductance = a := congrArg IntervalMedium.conductance E.medium_eq

theorem IntervalDesign.variable_share (E : IntervalDesign (variableUnitMedium a ha hapos) n K)
    (i : Fin n) : E.partition.width i = E.strength i * E.state (E.geometry.site i) := by
  have hi := E.partition_width i
  simpa only [StrictPartition.closed_width, OrderedMedium.stateShare, E.source_mass,
    variableUnitMedium_mass, div_one] using hi

theorem IntervalDesign.variable_cdfNode (E : IntervalDesign (variableUnitMedium a ha hapos) n K)
    (v : Fin (n + 2)) : cdfNode E.geometry.site v = E.geometry.node v := by
  refine Fin.cases ?_ (fun w => ?_) v
  · rw [cdfNode_first, E.geometry.node_first, E.variable_source]
    rfl
  · refine Fin.lastCases ?_ (fun i => ?_) w
    · change cdfNode E.geometry.site (Fin.last (n + 1)) = E.geometry.node (Fin.last (n + 1))
      rw [cdfNode_last, E.geometry.node_last, E.variable_source]
      rfl
    · exact cdfNode_site E.geometry.site i

theorem IntervalDesign.variable_site_mem (E : IntervalDesign (variableUnitMedium a ha hapos) n K)
    (i : Fin n) : E.geometry.site i ∈ Icc (0 : ℝ) 1 := by
  have hi := E.geometry.site_interior i
  rw [E.variable_source] at hi
  exact Ioo_subset_Icc_self hi

theorem IntervalDesign.variable_gradient_energy
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    (∫ x in (0 : ℝ)..1, a x * deriv E.state x * deriv E.state x) =
      weightedCDFScore (variableMeanWeight a ha hapos) E.partition.width E.geometry.site := by
  obtain ⟨j, hj⟩ := E.equation.to_strong (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos ⟨0, E.partition.size_pos⟩⟩
  have hshare : E.geometry.absorptionShare E.strength
      (fun v => E.state (E.geometry.node v)) = E.partition.width := by
    funext i
    exact (E.partition_width i).symm
  have hlocal (e : Fin (n + 1)) :
      (∫ t in (0 : ℝ)..E.geometry.gapLength e,
        a (E.geometry.node e.castSucc + t) * deriv E.state (E.geometry.node e.castSucc + t) *
          deriv E.state (E.geometry.node e.castSucc + t)) =
      ∫ z in cdfNode E.geometry.site e.castSucc..cdfNode E.geometry.site e.succ,
        (variableMeanWeight a ha hapos).value z * (absorptionPrefix E.partition.width e - z) ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..E.geometry.gapLength e,
          (variableMeanWeight a ha hapos).value (E.geometry.node e.castSucc + t) *
            (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) ^ 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (E.geometry.gapLength_pos e).le
        intro t ht
        have hd := ((hj.edge_equation e).state_derivative t ht).deriv
        rw [E.geometry.gapRestriction_deriv] at hd
        change deriv E.state (E.geometry.node e.castSucc + t) =
          j e t / E.geometry.conductance (E.geometry.node e.castSucc + t) at hd
        rw [E.variable_conductance] at hd
        have hf := E.geometry.absorption_flux hj e ht
        rw [E.geometry.absorptionCDF_gap _ e ht, hshare, E.variable_source,
          variableUnitMedium_mass, variableUnitMedium_coordinate, one_mul] at hf
        have hx := E.geometry.gap_point_mem e (Ioo_subset_Icc_self ht)
        rw [E.variable_source] at hx
        dsimp only
        rw [hd, hf]
        change a (E.geometry.node e.castSucc + t) *
          ((absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) /
            a (E.geometry.node e.castSucc + t)) *
          ((absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) /
            a (E.geometry.node e.castSucc + t)) =
          (1 / a (E.geometry.node e.castSucc + t)) *
            (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) ^ 2
        field_simp [ne_of_gt (hapos _ hx)]
      _ = _ := by
        change (∫ t in (0 : ℝ)..E.geometry.gapLength e,
          (fun z => (variableMeanWeight a ha hapos).value z *
            (absorptionPrefix E.partition.width e - z) ^ 2)
              (E.geometry.node e.castSucc + t)) = _
        rw [intervalIntegral.integral_comp_add_left
          (fun z => (variableMeanWeight a ha hapos).value z *
            (absorptionPrefix E.partition.width e - z) ^ 2)
          (E.geometry.node e.castSucc), add_zero,
          E.variable_cdfNode e.castSucc, E.variable_cdfNode e.succ]
        simp only [OrderedMedium.gapLength, add_sub_cancel]
  have hae : ContinuousOn a (uIcc E.geometry.source.left E.geometry.source.right) := by
    rw [E.variable_source]
    change ContinuousOn a (uIcc (0 : ℝ) 1)
    rwa [uIcc_of_le zero_le_one]
  have hi := E.equation.energy.bilinear_integrable E.equation.energy hae
  have hs := E.geometry.integral_gap_sum hi
  rw [E.variable_source] at hs
  change (∑ e, ∫ t in (0 : ℝ)..E.geometry.gapLength e,
    a (E.geometry.node e.castSucc + t) * deriv E.state (E.geometry.node e.castSucc + t) *
      deriv E.state (E.geometry.node e.castSucc + t)) =
    ∫ x in (0 : ℝ)..1, a x * deriv E.state x * deriv E.state x at hs
  rw [← hs]
  exact Finset.sum_congr rfl (fun e _ => hlocal e)

theorem variable_mean_energy (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    E.meanCost = (∑ i, E.partition.width i ^ 2 / E.strength i) +
      weightedCDFScore (variableMeanWeight a ha hapos) E.partition.width E.geometry.site := by
  have he := E.equation.weak_form E.state E.equation.energy
  rw [E.variable_source, E.variable_conductance] at he
  change (∫ x in (0 : ℝ)..1, a x * deriv E.state x * deriv E.state x) +
      (∑ i, E.strength i * E.state (E.geometry.site i) * E.state (E.geometry.site i)) =
        ∫ x in (0 : ℝ)..1, 1 * E.state x at he
  have hr : (∑ i, E.strength i * E.state (E.geometry.site i) * E.state (E.geometry.site i)) =
      ∑ i, E.partition.width i ^ 2 / E.strength i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [E.variable_share]
    field_simp [ne_of_gt (E.strength_pos i)]
  rw [hr, E.variable_gradient_energy] at he
  simp only [one_mul] at he
  change (∫ x in (0 : ℝ)..1, E.state x) / (1 - 0) = _
  rw [sub_zero, div_one, ← he, add_comm]

theorem variable_mean_canonical_deficit (hK : 0 < K)
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    E.meanCost - (1 / K + weightedCDFScore (variableMeanWeight a ha hapos)
      E.partition.width (weightedCDFMidpoint E.partition.width)) =
      meanStrengthLoss K E.strength E.partition.width +
      2 * ∑ i : Fin n, E.partition.width i *
        ∫ t in weightedCDFMidpoint E.partition.width i..E.geometry.site i,
          (variableMeanWeight a ha hapos).value t * (t - weightedCDFMidpoint E.partition.width i) := by
  rw [variable_mean_energy, weightedCDFScore_position_identity _ E.partition _ E.variable_site_mem]
  have hs := meanStrengthLoss_identity E.strength E.partition.width (ne_of_gt hK)
    (fun i => ne_of_gt (E.strength_pos i)) E.strength_sum E.partition.width_sum
  linarith

end TimeTraps.Interval
