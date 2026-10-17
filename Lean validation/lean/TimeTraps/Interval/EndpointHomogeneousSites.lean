module

public import TimeTraps.Interval.EndpointHomogeneousPartition
public import TimeTraps.Interval.HomogeneousMedium

@[expose] public section

/-! Exact cumulative side-count coordinates and all interior homogeneous
sites. A single formula covers both endpoint choices without excluding m=0. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

theorem EndpointArchitecture.homogeneousPartition_gapBoundary (A : EndpointArchitecture)
    (e : Fin (A.interiorCount + 1)) :
    A.homogeneousPartition.point (A.gapBoundary e) =
      ((A.leftReactive.toNat : ℝ) + 2 * (e.val : ℝ)) / A.sideTotal := by
  induction e using Fin.induction with
  | zero =>
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, add_zero]
    cases hl : A.leftReactive with
    | false =>
      have he : A.gapBoundary 0 = 0 := by apply Fin.ext; simp [gapBoundary, hl]
      rw [he, A.homogeneousPartition.first]
      simp only [Bool.toNat_false, Nat.cast_zero, zero_div]
    | true =>
      let i : Fin A.count := ⟨0, A.count_pos⟩
      have hi : A.kind i = .leftEndpoint := (A.kind_left_iff i).mpr ⟨hl, rfl⟩
      rw [← A.gapBoundary_left i hi]
      have hw := A.homogeneousPartition_width i
      change A.homogeneousPartition.point i.succ - A.homogeneousPartition.point i.castSucc = _ at hw
      have he : i.castSucc = 0 := rfl
      rw [he, A.homogeneousPartition.first, sub_zero] at hw
      simpa only [homogeneousShare, sideCount, hi, reduceCtorEq, if_false, hl,
        Bool.toNat_true, Nat.cast_one] using hw
  | succ i ih =>
    have hw := A.homogeneousPartition_width (A.interiorCell i)
    change A.homogeneousPartition.point (A.gapBoundary i.succ) -
      A.homogeneousPartition.point (A.gapBoundary i.castSucc) = _ at hw
    rw [homogeneousShare, A.sideCount_interior] at hw
    change A.homogeneousPartition.point (A.gapBoundary i.castSucc) =
      ((A.leftReactive.toNat : ℝ) + 2 * (i.val : ℝ)) / A.sideTotal at ih
    change A.homogeneousPartition.point (A.gapBoundary i.succ) =
      ((A.leftReactive.toNat : ℝ) + 2 * ((i.val + 1 : ℕ) : ℝ)) / A.sideTotal
    rw [Nat.cast_add, Nat.cast_one]
    calc
      _ = A.homogeneousPartition.point (A.gapBoundary i.castSucc) + 2 / A.sideTotal := by linarith
      _ = _ := by rw [ih]; ring

theorem EndpointArchitecture.homogeneousPartition_center (A : EndpointArchitecture)
    (W : CellWeight) {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (j : Fin A.interiorCount) :
    A.homogeneousPartition.center W (A.interiorCell j) =
      ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal := by
  unfold StrictPartition.center
  rw [W.center_constant hC (A.homogeneousPartition.point_mem _).1
    (A.homogeneousPartition.point_mem _).2 (A.homogeneousPartition.strictMono.monotone (Fin.castSucc_le_succ _))]
  change (A.homogeneousPartition.point (A.gapBoundary j.castSucc) +
    A.homogeneousPartition.point (A.gapBoundary j.succ)) / 2 = _
  rw [A.homogeneousPartition_gapBoundary, A.homogeneousPartition_gapBoundary]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem EndpointArchitecture.homogeneous_interior_sites (A : EndpointArchitecture)
    {L D : ℝ} (hL : 0 < L) (hD : 0 < D) (j : Fin A.interiorCount) :
    (homogeneous L D hL hD).partitionSites A.homogeneousPartition (A.interiorCell j) =
      L * ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal := by
  unfold IntervalMedium.partitionSites
  rw [homogeneous_inverse hL hD (Ioo_subset_Icc_self (A.homogeneousPartition.center_interior _ _))]
  rw [A.homogeneousPartition_center _ (fun z _ => homogeneous_weight hL hD z)]
  ring

end TimeTraps.Interval
