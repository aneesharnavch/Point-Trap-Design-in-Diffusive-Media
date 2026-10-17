module

public import TimeTraps.Interval.EndpointHomogeneousPartition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The endpoint-only example proves sharpness of the universal one-half
robustness constant for arbitrary positive continuous profiles. These
are exact integral identities, not decimal illustrations. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

theorem endpoint_leftOnly_root (Q : ClosedPartition EndpointArchitecture.leftOnly.count)
    (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    EndpointArchitecture.leftOnly.root Q W hb = 1 / b + W.rightRise 1 0 := by
  have hwidth (i : Fin EndpointArchitecture.leftOnly.count) : Q.width i = 1 := by
    have hi : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
    have he0 : i.castSucc = 0 := Fin.ext hi
    have he1 : i.succ = Fin.last EndpointArchitecture.leftOnly.count := by
      apply Fin.ext
      change i.val + 1 = 1
      omega
    change Q.point i.succ - Q.point i.castSucc = 1
    rw [he0, he1, Q.first, Q.last]
    norm_num
  have hbarrier (i : Fin EndpointArchitecture.leftOnly.count) :
      EndpointArchitecture.leftOnly.barrier Q W i = W.rightRise 1 0 := by
    have hi : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
    have he0 : i.castSucc = 0 := Fin.ext hi
    have he1 : i.succ = Fin.last EndpointArchitecture.leftOnly.count := by
      apply Fin.ext
      change i.val + 1 = 1
      omega
    change W.orientedBarrier (EndpointArchitecture.leftOnly.kind i) _ _ = _
    rw [EndpointArchitecture.leftOnly_kind]
    change W.rightRise (Q.point i.succ) (Q.point i.castSucc) = _
    rw [he0, he1, Q.first, Q.last]
  apply (EndpointArchitecture.leftOnly.eq_root Q W hb ?_ ?_).symm
  · intro i
    rw [hbarrier]
    linarith [one_div_pos.mpr hb]
  · unfold budget
    simp_rw [hwidth, hbarrier]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [EndpointArchitecture.leftOnly_count, Nat.cast_one, one_mul]
    rw [show 1 / b + W.rightRise 1 0 - W.rightRise 1 0 = 1 / b by ring]
    field_simp [ne_of_gt hb]

theorem endpoint_leftOnly_scalar_minimum (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    IsLeast (range (fun Q : ClosedPartition EndpointArchitecture.leftOnly.count =>
      EndpointArchitecture.leftOnly.root Q W hb)) (1 / b + W.rightRise 1 0) := by
  refine ⟨⟨EndpointArchitecture.leftOnly.homogeneousPartition.closed, endpoint_leftOnly_root _ W hb⟩, ?_⟩
  rintro M ⟨Q, rfl⟩
  change 1 / b + W.rightRise 1 0 ≤ EndpointArchitecture.leftOnly.root Q W hb
  rw [endpoint_leftOnly_root]

theorem CellWeight.rightRise_unit_additive_shift (W V : CellWeight) {ε : ℝ}
    (hshift : ∀ z ∈ Icc (0 : ℝ) 1, V.value z = W.value z + ε) :
    V.rightRise 1 0 - W.rightRise 1 0 = ε / 2 := by
  have hW : IntervalIntegrable (fun z => W.value z * (1 - z)) volume 0 1 :=
    (W.integrable ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).mul_continuousOn
      (continuous_const.sub continuous_id).continuousOn
  have hε : IntervalIntegrable (fun z : ℝ => ε * (1 - z)) volume 0 1 :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1
  have he : V.rightRise 1 0 = W.rightRise 1 0 + ∫ z in (0 : ℝ)..1, ε * (1 - z) := by
    change (∫ z in (0 : ℝ)..1, V.value z * (1 - z)) =
      (∫ z in (0 : ℝ)..1, W.value z * (1 - z)) + ∫ z in (0 : ℝ)..1, ε * (1 - z)
    rw [← intervalIntegral.integral_add hW hε]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro z hz
    dsimp only
    rw [hshift z (Ioo_subset_Icc_self hz)]
    ring
  rw [he, add_sub_cancel_left, intervalIntegral.integral_const_mul]
  have hlinear : (∫ x in (0 : ℝ)..1, (1 : ℝ) - x) =
      (∫ x in (0 : ℝ)..1, (1 : ℝ)) - ∫ x in (0 : ℝ)..1, x :=
    intervalIntegral.integral_sub intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)
  rw [hlinear, integral_id]
  norm_num
  ring

theorem endpoint_leftOnly_root_additive_shift
    (Q : ClosedPartition EndpointArchitecture.leftOnly.count) (W V : CellWeight)
    {b ε : ℝ} (hb : 0 < b)
    (hshift : ∀ z ∈ Icc (0 : ℝ) 1, V.value z = W.value z + ε) :
    EndpointArchitecture.leftOnly.root Q V hb - EndpointArchitecture.leftOnly.root Q W hb = ε / 2 := by
  rw [endpoint_leftOnly_root, endpoint_leftOnly_root, add_sub_add_left_eq_sub]
  exact W.rightRise_unit_additive_shift V hshift

end TimeTraps.Interval
