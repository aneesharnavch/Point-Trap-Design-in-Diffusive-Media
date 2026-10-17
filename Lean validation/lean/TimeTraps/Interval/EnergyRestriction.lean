module

public import TimeTraps.Interval.PhysicalEnergy

@[expose] public section

/-!
Arbitrary global energy tests restrict to the ordered gaps. Integration over
the physical interval equals the sum of the translated gap integrals.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Topology

variable {n : ℕ}

def OrderedMedium.gapRestriction (D : OrderedMedium n) (w : ℝ → ℝ)
    (e : Fin (n + 1)) (x : ℝ) : ℝ := w (D.node e.castSucc + x)

theorem OrderedMedium.restrict_energy (D : OrderedMedium n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w D.source.left D.source.right) :
    GraphEnergy D.graph (fun v => w (D.node v)) (D.gapRestriction w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have horder := (D.node_strictMono (Fin.castSucc_lt_succ (i := e))).le
    have he : IntervalEnergy w (D.node e.castSucc) (D.node e.succ) := hw.mono (by
      rw [uIcc_of_le horder, uIcc_of_le D.source.increasing.le]
      exact Icc_subset_Icc (D.node_mem e.castSucc).1 (D.node_mem e.succ).2)
    change IntervalEnergy (fun x => w (D.node e.castSucc + x)) 0
      (D.node e.succ - D.node e.castSucc)
    simpa only [sub_self] using he.translate horder (D.node e.castSucc)
  · intro e
    change w (D.node e.castSucc + 0) = w (D.node e.castSucc)
    rw [add_zero]
  · intro e
    change w (D.node e.castSucc + (D.node e.succ - D.node e.castSucc)) = w (D.node e.succ)
    rw [add_sub_cancel]

theorem OrderedMedium.gapRestriction_deriv (D : OrderedMedium n) (w : ℝ → ℝ)
    (e : Fin (n + 1)) (x : ℝ) :
    deriv (D.gapRestriction w e) x = deriv w (D.node e.castSucc + x) :=
  deriv_comp_const_add w (D.node e.castSucc) x

theorem OrderedMedium.assembledState_gap_deriv (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy D.graph U u) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) :
    deriv (D.assembledState U u) (D.node e.castSucc + x) = deriv (u e) x := by
  have he : D.gapRestriction (D.assembledState U u) e =ᶠ[nhds x] u e := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact D.assembledState_gap hu e ⟨hy.1.le, hy.2.le⟩
  rw [← D.gapRestriction_deriv]
  exact he.deriv_eq

theorem OrderedMedium.integral_gap_sum (D : OrderedMedium n) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume D.source.left D.source.right) :
    (∑ e, ∫ x in 0..D.gapLength e, g (D.node e.castSucc + x)) =
      ∫ x in D.source.left..D.source.right, g x := by
  have hi (v : Fin (n + 2)) : IntervalIntegrable g volume D.source.left (D.node v) :=
    hg.mono_set (uIcc_subset_uIcc_left (by
      simpa only [uIcc_of_le D.source.increasing.le] using D.node_mem v))
  have he (e : Fin (n + 1)) :
      (∫ x in 0..D.gapLength e, g (D.node e.castSucc + x)) =
        (∫ x in D.source.left..D.node e.succ, g x) -
        (∫ x in D.source.left..D.node e.castSucc, g x) := by
    rw [intervalIntegral.integral_comp_add_left, add_zero]
    simp only [OrderedMedium.gapLength, add_sub_cancel]
    exact (intervalIntegral.integral_interval_sub_left (hi e.succ) (hi e.castSucc)).symm
  simp_rw [he]
  rw [fin_sum_adjacent_difference (fun v => ∫ x in D.source.left..D.node v, g x)]
  rw [D.node_first, D.node_last, intervalIntegral.integral_same, sub_zero]

theorem OrderedMedium.source_test_integrable (D : OrderedMedium n) {v : ℝ → ℝ}
    (hv : IntervalEnergy v D.source.left D.source.right) :
    IntervalIntegrable (fun x => D.source.density x * v x) volume D.source.left D.source.right := by
  apply (D.source.continuous.mul ?_).intervalIntegrable_of_Icc D.source.increasing.le
  simpa only [uIcc_of_le D.source.increasing.le] using hv.continuousOn

end TimeTraps.Interval
