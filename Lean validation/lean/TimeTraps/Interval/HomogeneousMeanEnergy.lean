module

public import TimeTraps.Interval.HomogeneousDesign
public import TimeTraps.Interval.CDFSquare
public import TimeTraps.Interval.IntegralAssembly

@[expose] public section

/-!
The Lebesgue mean of every physical homogeneous weak design has an exact
reaction-plus-CDF energy representation. Its shares are those of the actual
weak solution. Neither optimality nor an independently selected share vector
is assumed, and the original full H1 weak equation supplies the self-test.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

theorem IntervalDesign.homogeneous_source
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.geometry.source = (homogeneous L D hL hD).source :=
  congrArg IntervalMedium.source E.medium_eq

theorem IntervalDesign.homogeneous_conductance
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.geometry.conductance = fun _ => D :=
  congrArg IntervalMedium.conductance E.medium_eq

theorem IntervalDesign.homogeneous_share
    (E : IntervalDesign (homogeneous L D hL hD) n K) (i : Fin n) :
    E.partition.width i = E.strength i * E.state (E.geometry.site i) / L := by
  have h := E.partition_width i
  simpa only [StrictPartition.closed_width, OrderedMedium.stateShare,
    E.source_mass, homogeneous_mass] using h

theorem IntervalDesign.homogeneous_cdfNode
    (E : IntervalDesign (homogeneous L D hL hD) n K) (v : Fin (n + 2)) :
    cdfNode (fun i => E.geometry.site i / L) v = E.geometry.node v / L := by
  refine Fin.cases ?_ (fun w => ?_) v
  · rw [cdfNode_first, E.geometry.node_first, E.homogeneous_source]
    change 0 = 0 / L
    simp
  · refine Fin.lastCases ?_ (fun i => ?_) w
    · change cdfNode (fun i => E.geometry.site i / L) (Fin.last (n + 1)) =
        E.geometry.node (Fin.last (n + 1)) / L
      rw [cdfNode_last, E.geometry.node_last, E.homogeneous_source]
      change 1 = L / L
      rw [div_self (ne_of_gt hL)]
    · exact cdfNode_site (fun i => E.geometry.site i / L) i

theorem integral_cdf_square_affine (q a b : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..b - a, (q - (a + t) / L) ^ 2) =
      L * ∫ z in a / L..b / L, (q - z) ^ 2 := by
  change (∫ t in (0 : ℝ)..b - a, (fun y => (q - y / L) ^ 2) (a + t)) = _
  rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => (q - y / L) ^ 2) a,
    add_zero, add_sub_cancel]
  rw [intervalIntegral.integral_comp_div (fun z : ℝ => (q - z) ^ 2) (ne_of_gt hL)]
  rfl

theorem IntervalDesign.homogeneous_gradient_energy
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    D * (∫ x in (0 : ℝ)..L, deriv E.state x ^ 2) =
      L ^ 3 / D * cdfSquareScore E.partition.width
        (fun i => E.geometry.site i / L) := by
  obtain ⟨j, hj⟩ := E.equation.to_strong (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos ⟨0, E.partition.size_pos⟩⟩
  have hshare : E.geometry.absorptionShare E.strength
      (fun v => E.state (E.geometry.node v)) = E.partition.width := by
    funext i
    exact (E.partition_width i).symm
  have hlocal (e : Fin (n + 1)) :
      (∫ t in (0 : ℝ)..E.geometry.gapLength e,
        deriv (E.geometry.gapRestriction E.state e) t ^ 2) =
      L ^ 3 / D ^ 2 *
        ∫ z in cdfNode (fun i => E.geometry.site i / L) e.castSucc..
          cdfNode (fun i => E.geometry.site i / L) e.succ,
          (absorptionPrefix E.partition.width e - z) ^ 2 := by
    have he : (∫ t in (0 : ℝ)..E.geometry.gapLength e,
        deriv (E.geometry.gapRestriction E.state e) t ^ 2) =
        (L ^ 2 / D ^ 2) * ∫ t in (0 : ℝ)..E.geometry.gapLength e,
          (absorptionPrefix E.partition.width e -
            (E.geometry.node e.castSucc + t) / L) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (E.geometry.gapLength_pos e).le
      intro t ht
      have hd := ((hj.edge_equation e).state_derivative t ht).deriv
      have hf := E.geometry.absorption_flux hj e ht
      rw [E.geometry.absorptionCDF_gap _ e ht, hshare, E.homogeneous_source,
        homogeneous_mass, homogeneous_coordinate] at hf
      change deriv (E.geometry.gapRestriction E.state e) t =
        j e t / E.geometry.conductance (E.geometry.node e.castSucc + t) at hd
      rw [E.homogeneous_conductance, hf] at hd
      dsimp only
      rw [hd]
      ring
    rw [he]
    change L ^ 2 / D ^ 2 *
      (∫ t in (0 : ℝ)..E.geometry.node e.succ - E.geometry.node e.castSucc,
        (absorptionPrefix E.partition.width e -
          (E.geometry.node e.castSucc + t) / L) ^ 2) = _
    rw [integral_cdf_square_affine _ _ _ hL,
      E.homogeneous_cdfNode e.castSucc, E.homogeneous_cdfNode e.succ]
    ring
  have hs := E.geometry.integral_gap_sum E.equation.energy.derivative_square_integrable
  rw [E.homogeneous_source] at hs
  change (∑ e, ∫ t in (0 : ℝ)..E.geometry.gapLength e,
      deriv E.state (E.geometry.node e.castSucc + t) ^ 2) =
    ∫ x in (0 : ℝ)..L, deriv E.state x ^ 2 at hs
  rw [← hs]
  simp_rw [← E.geometry.gapRestriction_deriv, hlocal]
  rw [← Finset.mul_sum]
  unfold cdfSquareScore
  field_simp [ne_of_gt hD]

theorem homogeneous_mean_energy
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    (∫ x in (0 : ℝ)..L, E.state x) / L =
      L * (∑ i, E.partition.width i ^ 2 / E.strength i) +
        L ^ 2 / D * cdfSquareScore E.partition.width
          (fun i => E.geometry.site i / L) := by
  have he := E.equation.weak_form E.state E.equation.energy
  rw [E.homogeneous_source, E.homogeneous_conductance] at he
  change (∫ x in (0 : ℝ)..L, D * deriv E.state x * deriv E.state x) +
    (∑ i, E.strength i * E.state (E.geometry.site i) * E.state (E.geometry.site i)) =
      ∫ x in (0 : ℝ)..L, 1 * E.state x at he
  have hr : (∑ i, E.strength i * E.state (E.geometry.site i) * E.state (E.geometry.site i)) =
      L ^ 2 * ∑ i, E.partition.width i ^ 2 / E.strength i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [E.homogeneous_share i]
    field_simp [ne_of_gt hL, ne_of_gt (E.strength_pos i)]
  have hg : (∫ x in (0 : ℝ)..L, D * deriv E.state x * deriv E.state x) =
      D * ∫ x in (0 : ℝ)..L, deriv E.state x ^ 2 := by
    simp only [pow_two, mul_assoc, intervalIntegral.integral_const_mul]
  rw [hr, hg, E.homogeneous_gradient_energy] at he
  simp only [one_mul] at he
  rw [← he]
  field_simp [ne_of_gt hL, ne_of_gt hD]
  ring

end TimeTraps.Interval
