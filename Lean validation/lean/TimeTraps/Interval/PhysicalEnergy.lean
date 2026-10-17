module

public import TimeTraps.Interval.GlobalState
public import TimeTraps.Analysis.IntervalEnergyLocal

@[expose] public section

/-!
The assembled physical state belongs to the independent global energy
space. Its derivative is assembled from the continuous gap flux/coefficient
ratios using disjoint open intervals; no global energy membership is assumed.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

noncomputable def OrderedMedium.gapDerivative (D : OrderedMedium n)
    (j : Fin (n + 1) → ℝ → ℝ) (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  j e (x - D.node e.castSucc) / D.conductance x

noncomputable def OrderedMedium.physicalSlope (D : OrderedMedium n)
    (j : Fin (n + 1) → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ e, (Ioo (D.node e.castSucc) (D.node e.succ)).indicator (D.gapDerivative j e) x

theorem OrderedMedium.not_other_open_gap (D : OrderedMedium n) {d e : Fin (n + 1)}
    (hde : d ≠ e) {x : ℝ} (hx : x ∈ Ioo (D.node e.castSucc) (D.node e.succ)) :
    x ∉ Ioo (D.node d.castSucc) (D.node d.succ) := by
  intro hd
  rcases lt_or_gt_of_ne hde with hlt | hgt
  · have hi : d.succ ≤ e.castSucc := by change d.val + 1 ≤ e.val; omega
    have hn := D.node_strictMono.monotone hi
    linarith [hx.1, hd.2]
  · have hi : e.succ ≤ d.castSucc := by change e.val + 1 ≤ d.val; omega
    have hn := D.node_strictMono.monotone hi
    linarith [hx.2, hd.1]

theorem OrderedMedium.physicalSlope_gap (D : OrderedMedium n)
    (j : Fin (n + 1) → ℝ → ℝ) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (D.node e.castSucc) (D.node e.succ)) :
    D.physicalSlope j x = j e (x - D.node e.castSucc) / D.conductance x := by
  classical
  unfold OrderedMedium.physicalSlope
  rw [Finset.sum_eq_single e]
  · simp only [indicator_of_mem hx, OrderedMedium.gapDerivative]
  · intro d _ hde
    exact indicator_of_notMem (D.not_other_open_gap hde hx) _
  · simp

theorem OrderedMedium.gapDerivative_continuous (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (e : Fin (n + 1)) :
    ContinuousOn (D.gapDerivative j e) (Icc (D.node e.castSucc) (D.node e.succ)) := by
  have hj := (h.edge_equation e).flux_continuous.comp
    (continuous_id.sub continuous_const).continuousOn
    (show MapsTo (fun x => x - D.node e.castSucc)
      (Icc (D.node e.castSucc) (D.node e.succ)) (Icc 0 (D.graph.length e)) from
      fun _ hx => ⟨sub_nonneg.mpr hx.1, sub_le_sub_right hx.2 _⟩)
  have hsub : Icc (D.node e.castSucc) (D.node e.succ) ⊆ Icc D.source.left D.source.right :=
    Icc_subset_Icc (D.node_mem e.castSucc).1 (D.node_mem e.succ).2
  exact hj.div (D.conductance_continuous.mono hsub)
    (fun x hx => ne_of_gt (D.conductance_pos x (hsub hx)))

theorem OrderedMedium.physicalSlope_memLp (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) : MemLp (D.physicalSlope j) 2 volume :=
  memLp_finsetSum Finset.univ (fun e _ => continuousOn_indicator_memLp_two (D.gapDerivative_continuous h e))

theorem OrderedMedium.physicalSlope_integrable (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    IntervalIntegrable (D.physicalSlope j) volume D.source.left D.source.right := by
  apply intervalIntegrable_iff.mpr
  let : IsFiniteMeasure (volume.restrict (uIoc D.source.left D.source.right)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [uIoc_of_le D.source.increasing.le]
      exact measure_Ioc_lt_top.ne)
  exact MemLp.integrable (by norm_num)
    ((D.physicalSlope_memLp h).restrict (uIoc D.source.left D.source.right))

theorem OrderedMedium.physicalSlope_square_integrable (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    IntervalIntegrable (fun x => D.physicalSlope j x ^ 2) volume D.source.left D.source.right :=
  intervalIntegrable_iff.mpr (D.physicalSlope_memLp h).integrable_sq.integrableOn

theorem OrderedMedium.assembledState_energy (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    IntervalEnergy (D.assembledState U u) D.source.left D.source.right := by
  apply intervalEnergy_of_derivative_off_countable D.source.increasing.le
    (finite_range D.site).countable (D.assembledState_continuous h.energy_membership).continuousOn
    (g := D.physicalSlope j)
  · intro x hx
    obtain ⟨e, he⟩ := D.gap_cover_open hx.1 (fun i hi => hx.2 ⟨i, hi⟩)
    rw [D.physicalSlope_gap j e he]
    exact D.assembledState_derivative h e he
  · exact D.physicalSlope_integrable h
  · exact D.physicalSlope_square_integrable h

end TimeTraps.Interval
