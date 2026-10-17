module

public import TimeTraps.Interval.CDFSquare
public import TimeTraps.Interval.StrictPartition

@[expose] public section

/-!
Exact weighted CDF cost and the oriented cost of moving every jump from its
cumulative-share midpoint. Telescoping primitives prove the identity without
assuming that the canonical score equals an independently defined grid cost.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

noncomputable def weightedCDFScore (W : CellWeight) (p x : Fin n → ℝ) : ℝ :=
  ∑ e : Fin (n + 1), ∫ z in cdfNode x e.castSucc..cdfNode x e.succ,
    W.value z * (absorptionPrefix p e - z) ^ 2

noncomputable def weightedCDFMidpoint (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  (absorptionPrefix p i.castSucc + absorptionPrefix p i.succ) / 2

theorem weightedCDFMidpoint_width (Q : StrictPartition n) (i : Fin n) :
    weightedCDFMidpoint Q.width i = (Q.point i.castSucc + Q.point i.succ) / 2 := by
  simp only [weightedCDFMidpoint, Q.prefix_width]

theorem weightedCDFMidpoint_mem (Q : StrictPartition n) (i : Fin n) :
    weightedCDFMidpoint Q.width i ∈ Icc (0 : ℝ) 1 := by
  rw [weightedCDFMidpoint_width]
  have hl := Q.point_mem i.castSucc
  have hr := Q.point_mem i.succ
  constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]

theorem cdfNode_mem (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (v : Fin (n + 2)) : cdfNode x v ∈ Icc (0 : ℝ) 1 := by
  refine Fin.cases ?_ (fun w => ?_) v
  · rw [cdfNode_first]
    exact ⟨le_rfl, zero_le_one⟩
  · refine Fin.lastCases ?_ (fun i => ?_) w
    · change cdfNode x (Fin.last (n + 1)) ∈ _
      rw [cdfNode_last]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [cdfNode_site]
      exact hx i

theorem weightedCDF_integrable (W : CellWeight) (q : ℝ) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => W.value t * (q - t) ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (W.continuous.mul ((continuousOn_const.sub continuousOn_id).pow 2)).mono
  intro t ht
  exact ⟨(le_min ha.1 hb.1).trans ht.1, ht.2.trans (max_le ha.2 hb.2)⟩

noncomputable def weightedCDFPrimitive (W : CellWeight) (q x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, W.value t * (q - t) ^ 2

theorem weightedCDFPrimitive_sub (W : CellWeight) (q : ℝ) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    weightedCDFPrimitive W q b - weightedCDFPrimitive W q a =
      ∫ t in a..b, W.value t * (q - t) ^ 2 :=
  intervalIntegral.integral_interval_sub_left
    (weightedCDF_integrable W q ⟨le_rfl, zero_le_one⟩ hb)
    (weightedCDF_integrable W q ⟨le_rfl, zero_le_one⟩ ha)

theorem weightedCDFScore_telescope (W : CellWeight) (p x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    weightedCDFScore W p x = weightedCDFPrimitive W (absorptionPrefix p (Fin.last n)) 1 +
      ∑ i : Fin n, (weightedCDFPrimitive W (absorptionPrefix p i.castSucc) (x i) -
        weightedCDFPrimitive W (absorptionPrefix p i.succ) (x i)) := by
  let A (e : Fin (n + 1)) := weightedCDFPrimitive W (absorptionPrefix p e) (cdfNode x e.castSucc)
  let B (e : Fin (n + 1)) := weightedCDFPrimitive W (absorptionPrefix p e) (cdfNode x e.succ)
  have hscore : weightedCDFScore W p x = ∑ e : Fin (n + 1), (B e - A e) := by
    unfold weightedCDFScore
    apply Finset.sum_congr rfl
    intro e _
    exact (weightedCDFPrimitive_sub W _ (cdfNode_mem x hx e.castSucc)
      (cdfNode_mem x hx e.succ)).symm
  have hsum : (∑ e : Fin (n + 1), (B e - A e)) = B (Fin.last n) - A 0 +
      ∑ i : Fin n, (B i.castSucc - A i.succ) := by
    simp only [Finset.sum_sub_distrib]
    rw [Fin.sum_univ_castSucc B, Fin.sum_univ_succ A]
    ring
  rw [hscore, hsum]
  simp only [A, B, Fin.castSucc_zero, cdfNode_first, cdfNode_site, cdfNode_site']
  change weightedCDFPrimitive W (absorptionPrefix p (Fin.last n)) (cdfNode x (Fin.last (n + 1))) -
    weightedCDFPrimitive W (absorptionPrefix p 0) 0 + _ = _
  rw [cdfNode_last]
  simp only [weightedCDFPrimitive, intervalIntegral.integral_same, sub_zero]

theorem weightedCDFScore_position_identity (W : CellWeight) (Q : StrictPartition n)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    weightedCDFScore W Q.width x =
      weightedCDFScore W Q.width (weightedCDFMidpoint Q.width) +
      2 * ∑ i : Fin n, Q.width i * ∫ t in weightedCDFMidpoint Q.width i..x i,
        W.value t * (t - weightedCDFMidpoint Q.width i) := by
  have hterm (i : Fin n) :
      weightedCDFPrimitive W (absorptionPrefix Q.width i.castSucc) (x i) -
        weightedCDFPrimitive W (absorptionPrefix Q.width i.succ) (x i) -
      (weightedCDFPrimitive W (absorptionPrefix Q.width i.castSucc) (weightedCDFMidpoint Q.width i) -
        weightedCDFPrimitive W (absorptionPrefix Q.width i.succ) (weightedCDFMidpoint Q.width i)) =
      2 * Q.width i * ∫ t in weightedCDFMidpoint Q.width i..x i,
        W.value t * (t - weightedCDFMidpoint Q.width i) := by
    calc
      _ = (weightedCDFPrimitive W (absorptionPrefix Q.width i.castSucc) (x i) -
          weightedCDFPrimitive W (absorptionPrefix Q.width i.castSucc) (weightedCDFMidpoint Q.width i)) -
        (weightedCDFPrimitive W (absorptionPrefix Q.width i.succ) (x i) -
          weightedCDFPrimitive W (absorptionPrefix Q.width i.succ) (weightedCDFMidpoint Q.width i)) := by ring
      _ = ∫ t in weightedCDFMidpoint Q.width i..x i,
          (W.value t * (absorptionPrefix Q.width i.castSucc - t) ^ 2 -
            W.value t * (absorptionPrefix Q.width i.succ - t) ^ 2) := by
        rw [weightedCDFPrimitive_sub W _ (weightedCDFMidpoint_mem Q i) (hx i),
          weightedCDFPrimitive_sub W _ (weightedCDFMidpoint_mem Q i) (hx i),
          intervalIntegral.integral_sub
            (weightedCDF_integrable W _ (weightedCDFMidpoint_mem Q i) (hx i))
            (weightedCDF_integrable W _ (weightedCDFMidpoint_mem Q i) (hx i))]
      _ = ∫ t in weightedCDFMidpoint Q.width i..x i,
          (2 * Q.width i) * (W.value t * (t - weightedCDFMidpoint Q.width i)) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [weightedCDFMidpoint, absorptionPrefix_succ]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [weightedCDFScore_telescope W Q.width x hx,
    weightedCDFScore_telescope W Q.width _ (weightedCDFMidpoint_mem Q),
    Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  linear_combination hterm i

theorem weightedCDF_oriented_reverse (W : CellWeight) (m x : ℝ) :
    (∫ t in m..x, W.value t * (t - m)) = W.rightRise m x := by
  rw [intervalIntegral.integral_symm]
  unfold CellWeight.rightRise
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem weightedCDF_oriented_nonneg (W : CellWeight) {m x : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ ∫ t in m..x, W.value t * (t - m) := by
  rcases lt_trichotomy m x with hlt | rfl | hlt
  · exact (W.leftRise_pos hm.1 hx.2 hlt).le
  · simp only [intervalIntegral.integral_same, le_refl]
  · rw [weightedCDF_oriented_reverse]
    exact (W.rightRise_pos hx.1 hm.2 hlt).le

theorem weightedCDF_oriented_zero_iff (W : CellWeight) {m x : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ t in m..x, W.value t * (t - m)) = 0 ↔ x = m := by
  constructor
  · intro he
    rcases lt_trichotomy m x with hlt | heq | hlt
    · exact False.elim ((ne_of_gt (W.leftRise_pos hm.1 hx.2 hlt)) he)
    · exact heq.symm
    · rw [weightedCDF_oriented_reverse] at he
      exact False.elim ((ne_of_gt (W.rightRise_pos hx.1 hm.2 hlt)) he)
  · rintro rfl
    exact intervalIntegral.integral_same

theorem weightedCDFScore_canonical_le (W : CellWeight) (Q : StrictPartition n)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    weightedCDFScore W Q.width (weightedCDFMidpoint Q.width) ≤ weightedCDFScore W Q.width x := by
  rw [weightedCDFScore_position_identity W Q x hx]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (Q.width_pos i).le
      (weightedCDF_oriented_nonneg W (weightedCDFMidpoint_mem Q i) (hx i)))))

theorem weightedCDFScore_eq_canonical_iff (W : CellWeight) (Q : StrictPartition n)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    weightedCDFScore W Q.width x = weightedCDFScore W Q.width (weightedCDFMidpoint Q.width) ↔
      ∀ i, x i = weightedCDFMidpoint Q.width i := by
  rw [weightedCDFScore_position_identity W Q x hx]
  have hn (i : Fin n) : 0 ≤ Q.width i * ∫ t in weightedCDFMidpoint Q.width i..x i,
      W.value t * (t - weightedCDFMidpoint Q.width i) :=
    mul_nonneg (Q.width_pos i).le
      (weightedCDF_oriented_nonneg W (weightedCDFMidpoint_mem Q i) (hx i))
  constructor
  · intro he
    have hz : (∑ i : Fin n, Q.width i * ∫ t in weightedCDFMidpoint Q.width i..x i,
        W.value t * (t - weightedCDFMidpoint Q.width i)) = 0 := by linarith
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).mp hz i (Finset.mem_univ i)
    exact (weightedCDF_oriented_zero_iff W (weightedCDFMidpoint_mem Q i) (hx i)).mp
      ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (Q.width_pos i)))
  · intro he
    simp only [he, intervalIntegral.integral_same, mul_zero, Finset.sum_const_zero, add_zero]

end TimeTraps.Interval
