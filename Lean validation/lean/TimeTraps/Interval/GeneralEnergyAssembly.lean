module

public import TimeTraps.Interval.IntegralAssembly

@[expose] public section

/-! Finite gluing for arbitrary H1 functions. Absolute continuity follows
from local fundamental-theorem identities, not merely almost-everywhere
differentiability. No continuous-derivative hypothesis is imposed. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {n : ℕ}

theorem OrderedMedium.energy_of_closed_gaps (D : OrderedMedium n) {w : ℝ → ℝ}
    (hw : ∀ e : Fin (n + 1), IntervalEnergy w (D.node e.castSucc) (D.node e.succ)) :
    IntervalEnergy w D.source.left D.source.right := by
  have hd : IntervalIntegrable (deriv w) volume D.source.left D.source.right := by
    apply D.integrable_of_gaps
    intro e
    simpa only [sub_self, OrderedMedium.gapLength] using
      (hw e).absolutelyContinuous.intervalIntegrable_deriv.comp_add_left (D.node e.castSucc)
  have hd₂ : IntervalIntegrable (fun x => deriv w x ^ 2) volume D.source.left D.source.right := by
    apply D.integrable_of_gaps
    intro e
    simpa only [sub_self, OrderedMedium.gapLength] using
      (hw e).derivative_square_integrable.comp_add_left (D.node e.castSucc)
  have hi (v : Fin (n + 2)) : IntervalIntegrable (deriv w) volume D.source.left (D.node v) :=
    hd.mono_set (uIcc_subset_uIcc_left (by
      simpa only [uIcc_of_le D.source.increasing.le] using D.node_mem v))
  have hn (v : Fin (n + 2)) :
      (∫ x in D.source.left..D.node v, deriv w x) = w (D.node v) - w D.source.left := by
    induction v using Fin.induction with
    | zero => rw [D.node_first, intervalIntegral.integral_same, sub_self]
    | succ i ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi i.castSucc)
        (hw i).absolutelyContinuous.intervalIntegrable_deriv, ih,
        (hw i).absolutelyContinuous.integral_deriv_eq_sub]
      ring
  have hp (x : ℝ) (hx : x ∈ Icc D.source.left D.source.right) :
      (∫ t in D.source.left..x, deriv w t) = w x - w D.source.left := by
    obtain ⟨e, he⟩ := D.gap_cover hx
    have hm : IntervalEnergy w (D.node e.castSucc) x := (hw e).mono (by
      rw [uIcc_of_le he.1, uIcc_of_le (D.node_strictMono Fin.castSucc_lt_succ).le]
      exact Icc_subset_Icc le_rfl he.2)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi e.castSucc)
      hm.absolutelyContinuous.intervalIntegrable_deriv, hn,
      hm.absolutelyContinuous.integral_deriv_eq_sub]
    ring
  have ha := (interval_absolutelyContinuous_const (w D.source.left) D.source.left D.source.right).fun_add
    (hd.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  refine ⟨interval_absolutelyContinuous_congr ha ?_, hd₂⟩
  intro x hx
  have hx' : x ∈ Icc D.source.left D.source.right := by
    simpa only [uIcc_of_le D.source.increasing.le] using hx
  change w D.source.left + (∫ t in D.source.left..x, deriv w t) = w x
  rw [hp x hx']
  ring

theorem OrderedMedium.energy_on_gap_of_restriction (D : OrderedMedium n) {w : ℝ → ℝ}
    (e : Fin (n + 1)) (hw : IntervalEnergy (D.gapRestriction w e) 0 (D.gapLength e)) :
    IntervalEnergy w (D.node e.castSucc) (D.node e.succ) := by
  have h := hw.translate (D.gapLength_pos e).le (-D.node e.castSucc)
  have hf : (fun x => D.gapRestriction w e (-D.node e.castSucc + x)) = w := by
    funext x
    simp only [gapRestriction, add_neg_cancel_left]
  rw [hf] at h
  simpa only [zero_sub, neg_neg, sub_neg_eq_add, zero_add, gapLength, sub_add_cancel] using h

theorem OrderedMedium.energy_iff_restrictions (D : OrderedMedium n) (w : ℝ → ℝ) :
    IntervalEnergy w D.source.left D.source.right ↔
      ∀ e, IntervalEnergy (D.gapRestriction w e) 0 (D.gapLength e) := by
  constructor
  · intro hw e
    exact (D.restrict_energy hw).edge_energy e
  · intro hw
    exact D.energy_of_closed_gaps (fun e => D.energy_on_gap_of_restriction e (hw e))

theorem OrderedMedium.assembledState_energy_general (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy D.graph U u) :
    IntervalEnergy (D.assembledState U u) D.source.left D.source.right := by
  apply (D.energy_iff_restrictions _).mpr
  intro e
  apply (hu.edge_energy e).congr
  intro x hx
  have hx' : x ∈ Icc 0 (D.gapLength e) := by
    simpa only [OrderedMedium.graph, uIcc_of_le (D.gapLength_pos e).le] using hx
  exact (D.assembledState_gap hu e hx').symm

end TimeTraps.Interval
