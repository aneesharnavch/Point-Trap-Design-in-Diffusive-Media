module

public import TimeTraps.Interval.AbsorptionCDF

@[expose] public section

/-!
Assembly of the actual ordered gap states into a single continuous physical
function. Constant extension of each gap and an exact telescoping sum give
agreement on every closed gap, including their common endpoints.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Topology

variable {n : ℕ}

theorem absorptionPrefix_adjacent_difference (A : Fin (n + 2) → ℝ) (e : Fin (n + 1)) :
    absorptionPrefix (fun d : Fin (n + 1) => A d.succ - A d.castSucc) e.castSucc =
      A e.castSucc - A 0 := by
  induction e using Fin.induction with
  | zero => simp [absorptionPrefix_zero]
  | succ i ih =>
    change absorptionPrefix (fun d : Fin (n + 1) => A d.succ - A d.castSucc) i.castSucc.succ = _
    rw [absorptionPrefix_succ, ih]
    change A i.castSucc.castSucc - A 0 + (A i.castSucc.succ - A i.castSucc.castSucc) =
      A i.castSucc.succ - A 0
    ring

noncomputable def OrderedMedium.gapProjection (D : OrderedMedium n) (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  projIcc 0 (D.gapLength e) (D.gapLength_pos e).le (x - D.node e.castSucc)

theorem OrderedMedium.gapProjection_mem (D : OrderedMedium n) (e : Fin (n + 1)) (x : ℝ) :
    D.gapProjection e x ∈ Icc 0 (D.gapLength e) :=
  (projIcc 0 (D.gapLength e) (D.gapLength_pos e).le (x - D.node e.castSucc)).property

theorem OrderedMedium.gapProjection_continuous (D : OrderedMedium n) (e : Fin (n + 1)) :
    Continuous (D.gapProjection e) :=
  continuous_subtype_val.comp (continuous_projIcc.comp (continuous_id.sub continuous_const))

theorem OrderedMedium.gapProjection_self (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc 0 (D.gapLength e)) : D.gapProjection e (D.node e.castSucc + x) = x := by
  unfold OrderedMedium.gapProjection
  simp only [add_sub_cancel_left, projIcc_of_mem (D.gapLength_pos e).le hx]

theorem OrderedMedium.gapProjection_before (D : OrderedMedium n) {d e : Fin (n + 1)}
    (hde : d < e) {x : ℝ} (hx : x ∈ Icc 0 (D.gapLength e)) :
    D.gapProjection d (D.node e.castSucc + x) = D.gapLength d := by
  have hi : d.succ ≤ e.castSucc := by change d.val + 1 ≤ e.val; omega
  have hnode := D.node_strictMono.monotone hi
  have hpos : D.gapLength d ≤ D.node e.castSucc + x - D.node d.castSucc := by
    unfold OrderedMedium.gapLength
    linarith [hx.1]
  unfold OrderedMedium.gapProjection
  rw [projIcc_of_right_le (D.gapLength_pos d).le hpos]

theorem OrderedMedium.gapProjection_after (D : OrderedMedium n) {d e : Fin (n + 1)}
    (hed : e < d) {x : ℝ} (hx : x ∈ Icc 0 (D.gapLength e)) :
    D.gapProjection d (D.node e.castSucc + x) = 0 := by
  have hi : e.succ ≤ d.castSucc := by change e.val + 1 ≤ d.val; omega
  have hnode := D.node_strictMono.monotone hi
  have hneg : D.node e.castSucc + x - D.node d.castSucc ≤ 0 := by
    have hright := hx.2
    unfold OrderedMedium.gapLength at hright
    linarith
  unfold OrderedMedium.gapProjection
  rw [projIcc_of_le_left (D.gapLength_pos d).le hneg]

noncomputable def OrderedMedium.assembledState (D : OrderedMedium n)
    (U : Fin (n + 2) → ℝ) (u : Fin (n + 1) → ℝ → ℝ) (x : ℝ) : ℝ :=
  U 0 + ∑ e, (u e (D.gapProjection e x) - U e.castSucc)

theorem OrderedMedium.assembledState_continuous (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u) :
    Continuous (D.assembledState U u) := by
  apply continuous_const.add
  apply continuous_finsetSum
  intro e _
  have hc : ContinuousOn (u e) (Icc 0 (D.gapLength e)) := by
    have hc := (h.edge_energy e).continuousOn
    change ContinuousOn (u e) (uIcc 0 (D.gapLength e)) at hc
    simpa only [uIcc_of_le (D.gapLength_pos e).le] using hc
  exact (hc.comp_continuous (D.gapProjection_continuous e) (D.gapProjection_mem e)).sub continuous_const

/-- The sum reconstructs each original gap exactly, including both traces. -/
theorem OrderedMedium.assembledState_gap (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Icc 0 (D.gapLength e)) :
    D.assembledState U u (D.node e.castSucc + x) = u e x := by
  classical
  have he : ∀ d : Fin (n + 1),
      u d (D.gapProjection d (D.node e.castSucc + x)) - U d.castSucc =
        (if d.val < e.val then U d.succ - U d.castSucc else 0) +
          (if d = e then u e x - U e.castSucc else 0) := by
    intro d
    rcases lt_trichotomy d e with hd | rfl | hd
    · rw [D.gapProjection_before hd hx]
      have hu := h.head_value d
      change u d (D.gapLength d) = U d.succ at hu
      rw [hu]
      simp [show d.val < e.val from hd, ne_of_lt hd]
    · rw [D.gapProjection_self _ hx]
      simp
    · rw [D.gapProjection_after hd hx]
      have hu := h.tail_value d
      change u d 0 = U d.castSucc at hu
      rw [hu]
      simp [show ¬ d.val < e.val from not_lt.mpr hd.le, ne_of_gt hd]
  unfold OrderedMedium.assembledState
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hp := absorptionPrefix_adjacent_difference U e
  change (∑ d : Fin (n + 1), if d.val < e.val then U d.succ - U d.castSucc else 0) =
    U e.castSucc - U 0 at hp
  rw [hp]
  simp

theorem OrderedMedium.assembledState_node (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u)
    (v : Fin (n + 2)) : D.assembledState U u (D.node v) = U v := by
  refine Fin.lastCases ?_ (fun e => ?_) v
  · have he := D.assembledState_gap h (Fin.last n) ⟨(D.gapLength_pos (Fin.last n)).le, le_rfl⟩
    have hu := h.head_value (Fin.last n)
    change u (Fin.last n) (D.gapLength (Fin.last n)) = U (Fin.last (n + 1)) at hu
    rw [hu] at he
    have hlast : (Fin.last n).succ = Fin.last (n + 1) := by ext; rfl
    simpa only [OrderedMedium.gapLength, add_sub_cancel, hlast] using he
  · have he := D.assembledState_gap h e ⟨le_rfl, (D.gapLength_pos e).le⟩
    have hu := h.tail_value e
    change u e 0 = U e.castSucc at hu
    simpa only [add_zero] using he.trans hu

/-- Agreement with a gap holds throughout its physical open interval. -/
theorem OrderedMedium.assembledState_eventually_gap (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (D.node e.castSucc) (D.node e.succ)) :
    D.assembledState U u =ᶠ[𝓝 x] fun y => u e (y - D.node e.castSucc) := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  have ht : y - D.node e.castSucc ∈ Icc 0 (D.gapLength e) := by
    unfold OrderedMedium.gapLength
    exact ⟨sub_nonneg.mpr hy.1.le, sub_le_sub_right hy.2.le _⟩
  simpa only [add_sub_cancel] using D.assembledState_gap h e ht

theorem OrderedMedium.assembledState_derivative (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (D.node e.castSucc) (D.node e.succ)) :
    HasDerivAt (D.assembledState U u) (j e (x - D.node e.castSucc) / D.conductance x) x := by
  have ht : x - D.node e.castSucc ∈ Ioo 0 (D.gapLength e) := by
    unfold OrderedMedium.gapLength
    exact ⟨sub_pos.mpr hx.1, sub_lt_sub_right hx.2 _⟩
  have hd := ((h.edge_equation e).state_derivative _ ht).comp x
    ((hasDerivAt_id x).sub_const (D.node e.castSucc))
  have hd' : HasDerivAt (fun y => u e (y - D.node e.castSucc))
      (j e (x - D.node e.castSucc) / D.conductance x) x := by
    simpa only [OrderedMedium.graph, add_sub_cancel, mul_one, Function.comp_def, id_eq] using hd
  exact hd'.congr_of_eventuallyEq (D.assembledState_eventually_gap h.energy_membership e hx)

end TimeTraps.Interval
