module

public import TimeTraps.Interval.HomogeneousOptimum
public import TimeTraps.Interval.ConstantProfile

@[expose] public section

/-!
The Lebesgue average of every homogeneous worst-start optimizer is
L/K + L²/(12Dn²). It is obtained by integrating the actual weak-state
profile. This does not assert the separate historical mean-optimum theorem.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {L D K : ℝ} {n : ℕ}

theorem homogeneous_construct_profile_left (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (i : Fin n) {z : ℝ}
    (hz : z ∈ Icc ((i.val : ℝ) / n) ((2 * (i.val : ℝ) + 1) / (2 * n))) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).state (L * z) =
      (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) - (L * z - (i.val : ℝ) * L / n) ^ 2 / (2 * D) := by
  let A := homogeneous L D hL hD
  let Q := StrictPartition.uniform n hn
  let M := Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)
  have hcell : z ∈ Icc (Q.point i.castSucc) (Q.center A.cellWeight i) := by
    rw [StrictPartition.uniform_center_constant A.cellWeight hn (fun t _ => homogeneous_weight hL hD t)]
    exact hz
  have hunit : z ∈ Icc (0 : ℝ) 1 :=
    ⟨(Q.point_mem i.castSucc).1.trans hcell.1, hcell.2.trans (Q.center_interior A.cellWeight i).2.le⟩
  have hs := A.partitionState_source Q M hunit
  rw [homogeneous_inverse hL hD hunit] at hs
  have hp := A.constant_profile_left Q (fun t _ => homogeneous_weight hL hD t) M i hcell
  have hM : M = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) := homogeneous_uniform_root hL hD hn hK
  change A.partitionState Q M (L * z) = _
  rw [hs, hp, hM]
  change (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) - (L ^ 2 / D) * (z - (i.val : ℝ) / n) ^ 2 / 2 = _
  ring

theorem homogeneous_construct_profile_right (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (i : Fin n) {z : ℝ}
    (hz : z ∈ Icc ((2 * (i.val : ℝ) + 1) / (2 * n)) (((i.val : ℝ) + 1) / n)) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).state (L * z) =
      (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) - (((i.val : ℝ) + 1) * L / n - L * z) ^ 2 / (2 * D) := by
  let A := homogeneous L D hL hD
  let Q := StrictPartition.uniform n hn
  let M := Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)
  have hcell : z ∈ Icc (Q.center A.cellWeight i) (Q.point i.succ) := by
    rw [StrictPartition.uniform_center_constant A.cellWeight hn (fun t _ => homogeneous_weight hL hD t)]
    change z ∈ Icc ((2 * (i.val : ℝ) + 1) / (2 * n)) (((i.val + 1 : ℕ) : ℝ) / n)
    simpa only [Nat.cast_add, Nat.cast_one] using hz
  have hunit : z ∈ Icc (0 : ℝ) 1 :=
    ⟨(Q.center_interior A.cellWeight i).1.le.trans hcell.1, hcell.2.trans (Q.point_mem i.succ).2⟩
  have hs := A.partitionState_source Q M hunit
  rw [homogeneous_inverse hL hD hunit] at hs
  have hp := A.constant_profile_right Q (fun t _ => homogeneous_weight hL hD t) M i hcell
  have hM : M = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) := homogeneous_uniform_root hL hD hn hK
  change A.partitionState Q M (L * z) = _
  rw [hs, hp, hM]
  change (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) -
    (L ^ 2 / D) * (((i.val + 1 : ℕ) : ℝ) / n - z) ^ 2 / 2 = _
  rw [Nat.cast_add, Nat.cast_one]
  ring

theorem homogeneous_construct_mean (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    (∫ x in (0 : ℝ)..L,
      ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).state x) / L =
      L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) := by
  let A := homogeneous L D hL hD
  let Q := StrictPartition.uniform n hn
  let M := Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)
  have hs := A.source.source_integral (A.partitionState_continuous Q M)
  have hv : (∫ z in (0 : ℝ)..1, A.source.transformed (A.partitionState Q M) z) =
      ∫ z in (0 : ℝ)..1, A.partitionProfile Q M z := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro z hz
    exact A.partitionState_source Q M (Ioo_subset_Icc_self hz)
  rw [hv, homogeneous_mass] at hs
  change (∫ x in (0 : ℝ)..L, 1 * A.partitionState Q M x) =
    L * ∫ z in (0 : ℝ)..1, A.partitionProfile Q M z at hs
  simp only [one_mul] at hs
  have hw : (∑ i, Q.width i ^ 3) = 1 / (n : ℝ) ^ 2 :=
    Q.closed.cubic_width_bound.2.mpr (fun i => StrictPartition.uniform_width hn i)
  have hM : M = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) :=
    homogeneous_uniform_root hL hD hn hK
  change (∫ x in (0 : ℝ)..L, A.partitionState Q M x) / L = _
  rw [hs, mul_div_cancel_left₀ _ (ne_of_gt hL),
    A.constant_profile_integral Q (fun z _ => homogeneous_weight hL hD z) M, hw, hM]
  ring

theorem IntervalDesign.state_eqOn_of_parameters {A : IntervalMedium} (E F : IntervalDesign A n K)
    (hx : ∀ i, E.geometry.site i = F.geometry.site i) (hκ : E.strength = F.strength) :
    EqOn E.state F.state (Icc A.source.left A.source.right) := by
  have hG := OrderedMedium.eq_of_medium_sites (E.medium_eq.trans F.medium_eq.symm) hx
  have hw := E.equation
  rw [hG, hκ] at hw
  have he := interval_weak_state_unique hw F.equation (fun i => (F.strength_pos i).le)
    ⟨⟨0, F.partition.size_pos⟩, F.strength_pos ⟨0, F.partition.size_pos⟩⟩
  have hs : F.geometry.source = A.source := congrArg IntervalMedium.source F.medium_eq
  simpa only [hs] using he

theorem homogeneous_optimal_mean (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) (hE : E.Optimal) :
    (∫ x in (0 : ℝ)..L, E.state x) / L = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) := by
  let F := (homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK
  have hp := (homogeneous_optimal_iff hL hD hn hK E).mp hE
  have he := E.state_eqOn_of_parameters F
    (fun i => (hp.1 i).trans (homogeneous_construct_sites hL hD hn hK i).symm)
    (funext (fun i => (hp.2 i).trans (homogeneous_construct_strength hL hD hn hK i).symm))
  have hi : (∫ x in (0 : ℝ)..L, E.state x) = ∫ x in (0 : ℝ)..L, F.state x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hL.le
    intro x hx
    exact he (Ioo_subset_Icc_self hx)
  rw [hi]
  exact homogeneous_construct_mean hL hD hn hK

theorem homogeneous_optimal_maximum_minus_mean (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) (hE : E.Optimal) :
    E.cost - (∫ x in (0 : ℝ)..L, E.state x) / L = L ^ 2 / (24 * D * (n : ℝ) ^ 2) := by
  have hc := (homogeneous_cost_eq_iff hL hD hn hK E).mpr
    ((homogeneous_optimal_iff hL hD hn hK E).mp hE)
  rw [hc, homogeneous_optimal_mean hL hD hn hK E hE]
  ring

end TimeTraps.Interval
