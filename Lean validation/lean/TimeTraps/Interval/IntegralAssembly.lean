module

public import TimeTraps.Interval.EnergyRestriction

@[expose] public section

/-! Integrability on every actual gap implies integrability on the whole
physical interval, without any continuity requirement on the integrand. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ}

theorem OrderedMedium.integrable_of_gaps (D : OrderedMedium n) {f : ℝ → ℝ}
    (hf : ∀ e, IntervalIntegrable (fun x => f (D.node e.castSucc + x)) volume 0 (D.gapLength e)) :
    IntervalIntegrable f volume D.source.left D.source.right := by
  have hlocal (e : Fin (n + 1)) : IntervalIntegrable f volume (D.node e.castSucc) (D.node e.succ) := by
    apply (IntervalIntegrable.comp_add_left_iff (c := D.node e.castSucc)).mp
    simpa only [sub_self, OrderedMedium.gapLength] using hf e
  have hprefix (e : Fin (n + 1)) : IntervalIntegrable f volume (D.node 0) (D.node e.succ) := by
    induction e using Fin.induction with
    | zero => exact hlocal 0
    | succ i ih => exact ih.trans (hlocal i.succ)
  have h := hprefix (Fin.last n)
  change IntervalIntegrable f volume (D.node 0) (D.node (Fin.last (n + 1))) at h
  rwa [D.node_first, D.node_last] at h

end TimeTraps.Interval
