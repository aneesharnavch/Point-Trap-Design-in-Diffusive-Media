module

public import TimeTraps.Interval.ConstantPartition
public import TimeTraps.Interval.HomogeneousMedium
public import TimeTraps.Interval.PhysicalDesign

@[expose] public section

/-!
The explicit equal-cell design on a homogeneous interval. The original weak
construction has midpoint sites, equal strengths, trap value L/K and physical
essential norm L/K + L²/(8Dn²), all obtained by exact substitution.
-/

namespace TimeTraps.Interval

open Set

variable {L D K : ℝ} {n : ℕ}

theorem homogeneous_normalized_height (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    1 / (K / (homogeneous L D hL hD).source.mass) + (L ^ 2 / D) / (8 * (n : ℝ) ^ 2) =
      L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) := by
  rw [homogeneous_mass]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [ne_of_gt hL, ne_of_gt hD, ne_of_gt hK, hn0]

theorem homogeneous_uniform_root (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    (StrictPartition.uniform n hn).closed.root (homogeneous L D hL hD).cellWeight
      (div_pos hK (homogeneous L D hL hD).source.mass_pos) =
      L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) := by
  rw [StrictPartition.uniform_constant_root _ hn (fun z _ => homogeneous_weight hL hD z)]
  exact homogeneous_normalized_height hL hD hn hK

theorem homogeneous_uniform_sites (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (i : Fin n) :
    (homogeneous L D hL hD).partitionSites (StrictPartition.uniform n hn) i =
      (2 * (i.val : ℝ) + 1) * L / (2 * n) := by
  let A := homogeneous L D hL hD
  let Q := StrictPartition.uniform n hn
  change A.source.inverse (Q.center A.cellWeight i) = _
  rw [homogeneous_inverse hL hD (Ioo_subset_Icc_self (Q.center_interior A.cellWeight i))]
  rw [StrictPartition.uniform_center_constant A.cellWeight hn (fun z _ => homogeneous_weight hL hD z)]
  ring

theorem homogeneous_uniform_barrier (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (i : Fin n) :
    (StrictPartition.uniform n hn).barrier (homogeneous L D hL hD).cellWeight i =
      L ^ 2 / (8 * D * (n : ℝ) ^ 2) := by
  let Q := StrictPartition.uniform n hn
  change Q.closed.barrier (homogeneous L D hL hD).cellWeight i = _
  rw [Q.closed.barrier_constant _ (fun z _ => homogeneous_weight hL hD z) i,
    Q.closed_width, StrictPartition.uniform_width]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [ne_of_gt hD, hn0]

theorem homogeneous_uniform_strength (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (i : Fin n) :
    (homogeneous L D hL hD).partitionStrength (StrictPartition.uniform n hn)
      ((StrictPartition.uniform n hn).closed.root (homogeneous L D hL hD).cellWeight
        (div_pos hK (homogeneous L D hL hD).source.mass_pos)) i = K / n := by
  rw [IntervalMedium.partitionStrength, homogeneous_uniform_root hL hD hn hK,
    homogeneous_uniform_barrier hL hD hn i, homogeneous_mass, StrictPartition.uniform_width]
  rw [add_sub_cancel_right]
  field_simp [ne_of_gt hL, ne_of_gt hK]

theorem homogeneous_construct_cost (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).cost =
      L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) := by
  rw [IntervalMedium.construct_cost]
  exact homogeneous_uniform_root hL hD hn hK

theorem homogeneous_construct_sites (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (i : Fin n) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).geometry.site i =
      (2 * (i.val : ℝ) + 1) * L / (2 * n) := by
  rw [IntervalMedium.construct_sites]
  exact homogeneous_uniform_sites hL hD hn i

theorem homogeneous_construct_strength (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (i : Fin n) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).strength i = K / n := by
  rw [IntervalMedium.construct_strength]
  exact homogeneous_uniform_strength hL hD hn hK i

theorem homogeneous_construct_trap_value (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (i : Fin n) :
    ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).state
      (((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).geometry.site i) = L / K := by
  let A := homogeneous L D hL hD
  let Q := StrictPartition.uniform n hn
  change A.partitionState Q (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos))
    ((A.partitionDesign Q).site i) = _
  rw [A.partitionState_trap, homogeneous_uniform_root hL hD hn hK,
    homogeneous_uniform_barrier hL hD hn i]
  ring

end TimeTraps.Interval
