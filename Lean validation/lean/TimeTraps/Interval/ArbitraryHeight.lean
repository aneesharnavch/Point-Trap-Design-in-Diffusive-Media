module

public import TimeTraps.Interval.TransformedIntegral
public import TimeTraps.Interval.HeightComparison

@[expose] public section

/-!
The arbitrary-design height barrier for the actual assembled ordered-path
state. The CDF comparisons, including sites outside their absorption cells,
are derived from ordered sites and positive actual absorption shares.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Classical

variable {n : ℕ}

noncomputable def OrderedMedium.cellWeight (D : OrderedMedium n) : CellWeight :=
  CellWeight.ofSource D.source D.conductance D.conductance_continuous D.conductance_pos

theorem OrderedMedium.sourceSite_strictMono (D : OrderedMedium n) : StrictMono D.sourceSite := by
  intro i j hij
  exact D.source.coordinate_strictMono (Ioo_subset_Icc_self (D.site_interior i))
    (Ioo_subset_Icc_self (D.site_interior j)) (D.site_strictMono hij)

theorem OrderedMedium.absorptionCDF_before (D : OrderedMedium n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : Fin n) {t : ℝ} (ht : t < D.sourceSite i) :
    D.absorptionCDF p t ≤ absorptionPrefix p i.castSucc := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < i.val
  · simp only [Fin.val_castSucc, if_pos hk]
    split_ifs <;> simp [hp k]
  · have hik : i ≤ k := by change i.val ≤ k.val; omega
    have hn : ¬ D.sourceSite k ≤ t := not_le.mpr (ht.trans_le (D.sourceSite_strictMono.monotone hik))
    simp only [Fin.val_castSucc, if_neg hk, if_neg hn, le_refl]

theorem OrderedMedium.absorptionCDF_after (D : OrderedMedium n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : Fin n) {t : ℝ} (ht : D.sourceSite i < t) :
    absorptionPrefix p i.succ ≤ D.absorptionCDF p t := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < i.val + 1
  · have hki : k ≤ i := by change k.val ≤ i.val; omega
    have hy : D.sourceSite k ≤ t := (D.sourceSite_strictMono.monotone hki).trans ht.le
    simp only [Fin.val_succ, if_pos hk, if_pos hy, le_refl]
  · simp only [Fin.val_succ, if_neg hk]
    split_ifs <;> simp [hp k]

theorem OrderedMedium.leftRise_bound (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 < κ i) (i : Fin n)
    (hac : D.absorptionPartition κ U i.castSucc ≤ D.sourceSite i) :
    D.cellWeight.leftRise (D.absorptionPartition κ U i.castSucc) (D.sourceSite i) ≤
      D.transformedState U u (D.absorptionPartition κ U i.castSucc) - U (trapNode i) := by
  let α := D.absorptionPartition κ U i.castSucc
  let c := D.sourceSite i
  have hα := D.absorptionPartition_mem h hκ i.castSucc
  have hc : c ∈ Icc (0 : ℝ) 1 := D.source.coordinate_mem (Ioo_subset_Icc_self (D.site_interior i))
  have hw := D.source.weight_continuous D.conductance_continuous D.conductance_pos
  have hi : IntervalIntegrable (fun t => D.source.weight D.conductance t * (t - α)) volume α c :=
    (hw.mul (continuous_id.sub continuous_const)).intervalIntegrable α c
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hac hi
    (D.transformedSlope_integrable κ U α c).neg (fun t ht => ?_)
  · change (∫ t in α..c, D.source.weight D.conductance t * (t - α)) ≤
      ∫ t in α..c, -(D.transformedSlope κ U t) at hm
    rw [intervalIntegral.integral_neg,
      D.transformedState_integral h (a := α) (b := c) hα.1 hc.2 hac] at hm
    change D.cellWeight.leftRise α c ≤ -(D.transformedState U u c - D.transformedState U u α) at hm
    dsimp only [c] at hm
    rw [D.transformedState_site h.energy_membership i] at hm
    linarith
  · have hb := D.absorptionCDF_before (D.absorptionShare κ U)
      (fun k => (D.absorptionShare_pos h hκ k).le) i ht.2
    change D.absorptionCDF (D.absorptionShare κ U) t ≤ α at hb
    have hm := mul_le_mul_of_nonneg_left hb
      (D.source.weight_pos D.conductance_pos t).le
    change D.source.weight D.conductance t * (t - α) ≤
      -(D.source.weight D.conductance t * (D.absorptionCDF (D.absorptionShare κ U) t - t))
    nlinarith only [hm]

theorem OrderedMedium.rightRise_bound (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 < κ i) (i : Fin n)
    (hcb : D.sourceSite i ≤ D.absorptionPartition κ U i.succ) :
    D.cellWeight.rightRise (D.absorptionPartition κ U i.succ) (D.sourceSite i) ≤
      D.transformedState U u (D.absorptionPartition κ U i.succ) - U (trapNode i) := by
  let β := D.absorptionPartition κ U i.succ
  let c := D.sourceSite i
  have hβ := D.absorptionPartition_mem h hκ i.succ
  have hc : c ∈ Icc (0 : ℝ) 1 := D.source.coordinate_mem (Ioo_subset_Icc_self (D.site_interior i))
  have hw := D.source.weight_continuous D.conductance_continuous D.conductance_pos
  have hi : IntervalIntegrable (fun t => D.source.weight D.conductance t * (β - t)) volume c β :=
    (hw.mul (continuous_const.sub continuous_id)).intervalIntegrable c β
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hcb hi
    (D.transformedSlope_integrable κ U c β) (fun t ht => ?_)
  · rw [D.transformedState_integral h (a := c) (b := β) hc.1 hβ.2 hcb] at hm
    change D.cellWeight.rightRise β c ≤ D.transformedState U u β - D.transformedState U u c at hm
    dsimp only [c] at hm
    rw [D.transformedState_site h.energy_membership i] at hm
    exact hm
  · have hb := D.absorptionCDF_after (D.absorptionShare κ U)
      (fun k => (D.absorptionShare_pos h hκ k).le) i ht.1
    change β ≤ D.absorptionCDF (D.absorptionShare κ U) t at hb
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hb t)
      (D.source.weight_pos D.conductance_pos t).le

/-- The arbitrary-design height barrier and its necessary equality conditions,
with M the independently defined attained maximum of the actual state. -/
theorem OrderedMedium.arbitrary_height_barrier (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    D.cellWeight.barrier (D.absorptionPartition κ U i.castSucc) (D.absorptionPartition κ U i.succ) ≤
      D.graph.stateMaximum u - U (trapNode i) ∧
    (D.graph.stateMaximum u - U (trapNode i) =
      D.cellWeight.barrier (D.absorptionPartition κ U i.castSucc) (D.absorptionPartition κ U i.succ) →
      D.sourceSite i = D.cellWeight.center (D.absorptionPartition κ U i.castSucc)
        (D.absorptionPartition κ U i.succ) ∧
      D.transformedState U u (D.absorptionPartition κ U i.castSucc) = D.graph.stateMaximum u ∧
      D.transformedState U u (D.absorptionPartition κ U i.succ) = D.graph.stateMaximum u) := by
  have hα := D.absorptionPartition_mem h hκ i.castSucc
  have hβ := D.absorptionPartition_mem h hκ i.succ
  have hab := D.absorptionPartition_strictMono h hκ (Fin.castSucc_lt_succ (i := i))
  have hc := D.source.coordinate_mem (Ioo_subset_Icc_self (D.site_interior i))
  have hM : ∀ z ∈ Icc (0 : ℝ) 1, D.transformedState U u z ≤ D.graph.stateMaximum u := by
    intro z hz
    apply h.energy_membership.maximum_isGreatest.2
    rw [← D.transformedState_values h.energy_membership]
    exact ⟨z, hz, rfl⟩
  exact D.cellWeight.height_comparison hα.1 hβ.2 hab hc (hM _ hα) (hM _ hβ)
    (D.leftRise_bound h hκ i) (D.rightRise_bound h hκ i)

theorem OrderedMedium.weak_height_barrier (D : OrderedMedium n) (hn : 0 < n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (h : WeakGraphEquation D.graph (nodalStrength κ) U u) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    D.cellWeight.barrier (D.absorptionPartition κ U i.castSucc) (D.absorptionPartition κ U i.succ) ≤
      D.graph.stateMaximum u - U (trapNode i) := by
  obtain ⟨j, hj⟩ := h.to_strong (nodalStrength_nonneg κ (fun k => (hκ k).le))
    (nodalStrength_anchor κ ⟨⟨0, hn⟩, hκ ⟨0, hn⟩⟩)
  exact (D.arbitrary_height_barrier hj hκ i).1

theorem OrderedMedium.weak_height_equality (D : OrderedMedium n) (hn : 0 < n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (h : WeakGraphEquation D.graph (nodalStrength κ) U u) (hκ : ∀ i, 0 < κ i) (i : Fin n)
    (he : D.graph.stateMaximum u - U (trapNode i) =
      D.cellWeight.barrier (D.absorptionPartition κ U i.castSucc) (D.absorptionPartition κ U i.succ)) :
    D.sourceSite i = D.cellWeight.center (D.absorptionPartition κ U i.castSucc)
      (D.absorptionPartition κ U i.succ) ∧
    D.transformedState U u (D.absorptionPartition κ U i.castSucc) = D.graph.stateMaximum u ∧
    D.transformedState U u (D.absorptionPartition κ U i.succ) = D.graph.stateMaximum u := by
  obtain ⟨j, hj⟩ := h.to_strong (nodalStrength_nonneg κ (fun k => (hκ k).le))
    (nodalStrength_anchor κ ⟨⟨0, hn⟩, hκ ⟨0, hn⟩⟩)
  exact (D.arbitrary_height_barrier hj hκ i).2 he

end TimeTraps.Interval
