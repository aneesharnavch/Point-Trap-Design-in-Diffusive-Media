module

public import TimeTraps.Interval.PhysicalNorm
public import TimeTraps.Interval.ArbitraryHeight

@[expose] public section

/-!
Conservation, source-coordinate identities, and the arbitrary-design height
barrier for the independently defined single-interval H1 weak equation.
The height is the physical Lebesgue essential norm.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

noncomputable def OrderedMedium.stateShare (D : OrderedMedium n) (κ : Fin n → ℝ)
    (w : ℝ → ℝ) (i : Fin n) : ℝ := κ i * w (D.site i) / D.source.mass

noncomputable def OrderedMedium.statePartition (D : OrderedMedium n) (κ : Fin n → ℝ)
    (w : ℝ → ℝ) (e : Fin (n + 1)) : ℝ := absorptionPrefix (D.stateShare κ w) e

theorem OrderedMedium.assembledRestriction_eq (D : OrderedMedium n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w D.source.left D.source.right) :
    EqOn (D.assembledState (fun v => w (D.node v)) (D.gapRestriction w)) w
      (Icc D.source.left D.source.right) := by
  intro x hx
  obtain ⟨e, he⟩ := D.gap_cover hx
  have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  simpa only [OrderedMedium.gapRestriction, add_sub_cancel] using
    D.assembledState_gap (D.restrict_energy hw) e ht

theorem OrderedMedium.transformedRestriction_eq (D : OrderedMedium n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w D.source.left D.source.right) :
    D.transformedState (fun v => w (D.node v)) (D.gapRestriction w) = D.source.transformed w := by
  funext z
  exact D.assembledRestriction_eq hw (D.source.inverse_mem z)

theorem WeakIntervalEquation.conservation {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) : (∑ i, κ i * w (D.site i)) = D.source.mass := by
  have h := hw.weak_form (fun _ => 1) (IntervalEnergy.const 1 _ _)
  simpa [SourceInterval.mass] using h

theorem WeakIntervalEquation.reflecting_flux_and_jumps {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    ∃ j, GraphEquation D.graph (nodalStrength κ) (fun v => w (D.node v)) (D.gapRestriction w) j ∧
      j 0 0 = 0 ∧ j (Fin.last n) (D.gapLength (Fin.last n)) = 0 ∧
      ∀ i : Fin n, j i.succ 0 - j i.castSucc (D.gapLength i.castSucc) = κ i * w (D.site i) := by
  obtain ⟨j, hj⟩ := hw.to_strong hκ hanchor
  exact ⟨j, hj, (D.reflecting_endpoints hj).1, (D.reflecting_endpoints hj).2, D.flux_jump hj⟩

theorem WeakIntervalEquation.stateShare_sum {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) : (∑ i, D.stateShare κ w i) = 1 := by
  unfold OrderedMedium.stateShare
  rw [← Finset.sum_div, hw.conservation, div_self (ne_of_gt D.source.mass_pos)]

theorem WeakIntervalEquation.stateShare_pos {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    0 < D.stateShare κ w i := by
  exact div_pos (mul_pos (hκ i) (hw.positive (fun k => (hκ k).le) ⟨i, hκ i⟩ _
    (Ioo_subset_Icc_self (D.site_interior i)))) D.source.mass_pos

theorem OrderedMedium.statePartition_first (D : OrderedMedium n) (κ : Fin n → ℝ) (w : ℝ → ℝ) :
    D.statePartition κ w 0 = 0 := absorptionPrefix_zero _

theorem WeakIntervalEquation.statePartition_last {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) : D.statePartition κ w (Fin.last n) = 1 := by
  rw [OrderedMedium.statePartition, absorptionPrefix_last, hw.stateShare_sum]

theorem WeakIntervalEquation.statePartition_strictMono {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) :
    StrictMono (D.statePartition κ w) := absorptionPrefix_strictMono _ (hw.stateShare_pos hκ)

theorem WeakIntervalEquation.statePartition_mem {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i)
    (e : Fin (n + 1)) : D.statePartition κ w e ∈ Icc 0 1 := by
  rw [← D.statePartition_first κ w, ← hw.statePartition_last]
  exact ⟨(hw.statePartition_strictMono hκ).monotone (Fin.zero_le e),
    (hw.statePartition_strictMono hκ).monotone (Fin.le_last e)⟩

theorem WeakIntervalEquation.transformed_derivative {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hsite : ∀ i, D.sourceSite i ≠ z) :
    HasDerivAt (D.source.transformed w)
      (D.source.weight D.conductance z * (D.absorptionCDF (D.stateShare κ w) z - z)) z := by
  obtain ⟨j, hj⟩ := hw.to_strong hκ hanchor
  have hd := D.transformedState_derivative hj hz hsite
  rw [D.transformedRestriction_eq hw.energy] at hd
  exact hd

theorem WeakIntervalEquation.transformed_integral {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    (∫ z in a..b, D.source.weight D.conductance z * (D.absorptionCDF (D.stateShare κ w) z - z)) =
      D.source.transformed w b - D.source.transformed w a := by
  obtain ⟨j, hj⟩ := hw.to_strong hκ hanchor
  have hi := D.transformedState_integral hj ha hb hab
  rw [D.transformedRestriction_eq hw.energy] at hi
  exact hi

theorem WeakIntervalEquation.transformed_absolutelyContinuous {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    AbsolutelyContinuousOnInterval (D.source.transformed w) 0 1 := by
  obtain ⟨j, hj⟩ := hw.to_strong hκ hanchor
  have hi := D.transformedState_absolutelyContinuous hj
  rwa [D.transformedRestriction_eq hw.energy] at hi

theorem WeakIntervalEquation.height_barrier {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    D.cellWeight.barrier (D.statePartition κ w i.castSucc) (D.statePartition κ w i.succ) ≤
      D.essentialNorm w - w (D.site i) := by
  obtain ⟨j, hj⟩ := hw.to_strong (fun k => (hκ k).le) ⟨i, hκ i⟩
  have hb := (D.arbitrary_height_barrier hj hκ i).1
  rw [hw.maximum_eq_essentialNorm (fun k => (hκ k).le) ⟨i, hκ i⟩] at hb
  exact hb

theorem WeakIntervalEquation.height_equality {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n)
    (he : D.essentialNorm w - w (D.site i) =
      D.cellWeight.barrier (D.statePartition κ w i.castSucc) (D.statePartition κ w i.succ)) :
    D.sourceSite i = D.cellWeight.center (D.statePartition κ w i.castSucc) (D.statePartition κ w i.succ) ∧
      D.source.transformed w (D.statePartition κ w i.castSucc) = D.essentialNorm w ∧
      D.source.transformed w (D.statePartition κ w i.succ) = D.essentialNorm w := by
  obtain ⟨j, hj⟩ := hw.to_strong (fun k => (hκ k).le) ⟨i, hκ i⟩
  have hb := (D.arbitrary_height_barrier hj hκ i).2
  rw [hw.maximum_eq_essentialNorm (fun k => (hκ k).le) ⟨i, hκ i⟩,
    D.transformedRestriction_eq hw.energy] at hb
  exact hb he

end TimeTraps.Interval
