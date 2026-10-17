module

public import TimeTraps.Interval.SourceMeanTransport

@[expose] public section

/-!
The source-weighted mean of an arbitrary physical weak design. The CDF energy
is derived by self-testing the full H1 weak equation and transporting its
derived physical gap flux. No prescribed profile is an admissibility premise.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {A : IntervalMedium} {K : ℝ}

theorem IntervalDesign.source_gradient_energy (E : IntervalDesign A n K) :
    (∫ x in A.source.left..A.source.right,
      A.conductance x * deriv E.state x * deriv E.state x) =
      A.source.mass * weightedCDFScore A.cellWeight E.partition.width E.geometry.sourceSite := by
  obtain ⟨j, hj⟩ := E.equation.to_strong (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos ⟨0, E.partition.size_pos⟩⟩
  have hshare : E.geometry.absorptionShare E.strength
      (fun v => E.state (E.geometry.node v)) = E.partition.width := by
    funext i
    exact (E.partition_width i).symm
  have hnode (v : Fin (n + 2)) : E.geometry.node v ∈ Icc A.source.left A.source.right := by
    rw [← E.source_eq]
    exact E.geometry.node_mem v
  have hlocal (e : Fin (n + 1)) :
      (∫ t in (0 : ℝ)..E.geometry.gapLength e,
        A.conductance (E.geometry.node e.castSucc + t) * deriv E.state (E.geometry.node e.castSucc + t) *
          deriv E.state (E.geometry.node e.castSucc + t)) =
      A.source.mass * ∫ z in cdfNode E.geometry.sourceSite e.castSucc..cdfNode E.geometry.sourceSite e.succ,
        A.cellWeight.value z * (absorptionPrefix E.partition.width e - z) ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..E.geometry.gapLength e, A.source.mass *
          ((A.source.mass / A.conductance (E.geometry.node e.castSucc + t)) *
            (absorptionPrefix E.partition.width e - A.source.coordinate (E.geometry.node e.castSucc + t)) ^ 2) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (E.geometry.gapLength_pos e).le
        intro t ht
        have hd := ((hj.edge_equation e).state_derivative t ht).deriv
        rw [E.geometry.gapRestriction_deriv] at hd
        change deriv E.state (E.geometry.node e.castSucc + t) =
          j e t / E.geometry.conductance (E.geometry.node e.castSucc + t) at hd
        rw [E.conductance_eq] at hd
        have hf := E.geometry.absorption_flux hj e ht
        rw [E.geometry.absorptionCDF_gap _ e ht, hshare, E.source_eq] at hf
        have hx := E.geometry.gap_point_mem e (Ioo_subset_Icc_self ht)
        rw [E.source_eq] at hx
        dsimp only
        rw [hd, hf]
        field_simp [ne_of_gt (A.conductance_pos _ hx)]
      _ = A.source.mass * ∫ t in (0 : ℝ)..E.geometry.gapLength e,
          (A.source.mass / A.conductance (E.geometry.node e.castSucc + t)) *
            (absorptionPrefix E.partition.width e - A.source.coordinate (E.geometry.node e.castSucc + t)) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      _ = A.source.mass * ∫ x in E.geometry.node e.castSucc..E.geometry.node e.succ,
          (A.source.mass / A.conductance x) * (absorptionPrefix E.partition.width e - A.source.coordinate x) ^ 2 := by
        rw [intervalIntegral.integral_comp_add_left
          (fun x => (A.source.mass / A.conductance x) *
            (absorptionPrefix E.partition.width e - A.source.coordinate x) ^ 2)
          (E.geometry.node e.castSucc), add_zero]
        simp only [OrderedMedium.gapLength, add_sub_cancel]
      _ = _ := by
        rw [E.source_cdfNode e.castSucc, E.source_cdfNode e.succ]
        exact congrArg (fun v => A.source.mass * v)
          (source_mean_gap_transport A.source A.conductance_continuous A.conductance_pos
            (hnode e.castSucc) (hnode e.succ) (E.geometry.node_strictMono Fin.castSucc_lt_succ).le _)
  have hae : ContinuousOn A.conductance (uIcc E.geometry.source.left E.geometry.source.right) := by
    rw [E.source_eq, uIcc_of_le A.source.increasing.le]
    exact A.conductance_continuous
  have hi := E.equation.energy.bilinear_integrable E.equation.energy hae
  have hs := E.geometry.integral_gap_sum hi
  rw [E.source_eq] at hs
  change (∑ e, ∫ t in (0 : ℝ)..E.geometry.gapLength e,
    A.conductance (E.geometry.node e.castSucc + t) * deriv E.state (E.geometry.node e.castSucc + t) *
      deriv E.state (E.geometry.node e.castSucc + t)) =
    ∫ x in A.source.left..A.source.right,
      A.conductance x * deriv E.state x * deriv E.state x at hs
  rw [← hs, weightedCDFScore, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => hlocal e)

theorem source_mean_energy (E : IntervalDesign A n K) :
    E.sourceMeanCost = A.source.mass * (∑ i, E.partition.width i ^ 2 / E.strength i) +
      weightedCDFScore A.cellWeight E.partition.width E.geometry.sourceSite := by
  have he := E.equation.weak_form E.state E.equation.energy
  rw [E.source_eq, E.conductance_eq] at he
  have hr : (∑ i, E.strength i * E.state (E.geometry.site i) * E.state (E.geometry.site i)) =
      A.source.mass ^ 2 * ∑ i, E.partition.width i ^ 2 / E.strength i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [E.source_share]
    field_simp [ne_of_gt (E.strength_pos i), ne_of_gt A.source.mass_pos]
  rw [hr, E.source_gradient_energy] at he
  rw [IntervalDesign.sourceMeanCost, ← he]
  field_simp [ne_of_gt A.source.mass_pos]
  ring

end TimeTraps.Interval
