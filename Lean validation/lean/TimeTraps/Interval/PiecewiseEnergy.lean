module

public import TimeTraps.Interval.EnergyRestriction

@[expose] public section

/-!
Assembly of arbitrary matching gap functions with continuous gap derivatives.
The resulting global function belongs to the original interval energy space.
No source equation is assumed; the lemma applies in particular to spectral
states whose second derivative has the eigenvalue-dependent right-hand side.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Topology

variable {n : ℕ}

noncomputable def OrderedMedium.assembledSlope (D : OrderedMedium n)
    (g : Fin (n + 1) → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ e, (Ioo (D.node e.castSucc) (D.node e.succ)).indicator (fun y => g e (y - D.node e.castSucc)) x

theorem OrderedMedium.assembledSlope_gap (D : OrderedMedium n)
    (g : Fin (n + 1) → ℝ → ℝ) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (D.node e.castSucc) (D.node e.succ)) :
    D.assembledSlope g x = g e (x - D.node e.castSucc) := by
  classical
  unfold assembledSlope
  rw [Finset.sum_eq_single e]
  · exact indicator_of_mem hx _
  · intro d _ hde
    exact indicator_of_notMem (D.not_other_open_gap hde hx) _
  · simp

theorem OrderedMedium.assembledSlope_memLp (D : OrderedMedium n)
    {g : Fin (n + 1) → ℝ → ℝ}
    (hg : ∀ e, ContinuousOn (g e) (Icc (0 : ℝ) (D.gapLength e))) :
    MemLp (D.assembledSlope g) 2 volume := by
  apply memLp_finsetSum Finset.univ
  intro e _
  apply continuousOn_indicator_memLp_two
  exact (hg e).comp (continuous_id.sub continuous_const).continuousOn
    (fun x hx => ⟨sub_nonneg.mpr hx.1, sub_le_sub_right hx.2 _⟩)

theorem OrderedMedium.assembledState_piecewise_hasDerivAt (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u g : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy D.graph U u)
    (hd : ∀ e, ∀ x ∈ Ioo (0 : ℝ) (D.gapLength e), HasDerivAt (u e) (g e x) x)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (D.node e.castSucc) (D.node e.succ)) :
    HasDerivAt (D.assembledState U u) (g e (x - D.node e.castSucc)) x := by
  have ht : x - D.node e.castSucc ∈ Ioo (0 : ℝ) (D.gapLength e) :=
    ⟨sub_pos.mpr hx.1, sub_lt_sub_right hx.2 _⟩
  have h := (hd e _ ht).comp x ((hasDerivAt_id x).sub_const (D.node e.castSucc))
  have hh : HasDerivAt (fun y => u e (y - D.node e.castSucc)) (g e (x - D.node e.castSucc)) x := by
    simpa only [mul_one, Function.comp_def, id_eq] using h
  exact hh.congr_of_eventuallyEq (D.assembledState_eventually_gap hu e hx)

theorem OrderedMedium.assembledState_energy_of_piecewise (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u g : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy D.graph U u)
    (hg : ∀ e, ContinuousOn (g e) (Icc (0 : ℝ) (D.gapLength e)))
    (hd : ∀ e, ∀ x ∈ Ioo (0 : ℝ) (D.gapLength e), HasDerivAt (u e) (g e x) x) :
    IntervalEnergy (D.assembledState U u) D.source.left D.source.right := by
  let : IsFiniteMeasure (volume.restrict (uIoc D.source.left D.source.right)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [uIoc_of_le D.source.increasing.le]
      exact measure_Ioc_lt_top.ne)
  have hm := (D.assembledSlope_memLp hg).restrict (uIoc D.source.left D.source.right)
  apply intervalEnergy_of_derivative_off_countable D.source.increasing.le
    (finite_range D.site).countable (D.assembledState_continuous hu).continuousOn
    (g := D.assembledSlope g)
  · intro x hx
    obtain ⟨e, he⟩ := D.gap_cover_open hx.1 (fun i hi => hx.2 ⟨i, hi⟩)
    rw [D.assembledSlope_gap g e he]
    exact D.assembledState_piecewise_hasDerivAt hu hd e he
  · exact intervalIntegrable_iff.mpr (hm.integrable (by norm_num))
  · exact intervalIntegrable_iff.mpr hm.integrable_sq

end TimeTraps.Interval
