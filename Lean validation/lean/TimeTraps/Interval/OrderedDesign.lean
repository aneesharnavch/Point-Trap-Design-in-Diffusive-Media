module

public import TimeTraps.Graph.WeakState
public import TimeTraps.Analysis.SourceCoordinate
public import Mathlib.Order.Fin.Tuple

@[expose] public section

/-!
An ordered physical interval with n interior sites and n+1 gaps. The medium,
sites, and strengths are independent input data. The path graph is derived
from their actual positions; no flux law or state formula is assumed.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

theorem path_connected (n : ℕ) :
    IncidenceConnected (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) Fin.succ := by
  have hzero : ∀ v : Fin (n + 2), Relation.EqvGen
      (fun v w => ∃ e : Fin (n + 1), e.castSucc = v ∧ e.succ = w) 0 v := by
    intro v
    induction v using Fin.induction with
    | zero => exact Relation.EqvGen.refl 0
    | succ i ih =>
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ⟨i, rfl, rfl⟩)
  intro v w
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hzero v)) (hzero w)

structure OrderedMedium (n : ℕ) where
  source : SourceInterval
  conductance : ℝ → ℝ
  conductance_continuous : ContinuousOn conductance (Icc source.left source.right)
  conductance_pos : ∀ x ∈ Icc source.left source.right, 0 < conductance x
  node : Fin (n + 2) → ℝ
  node_strictMono : StrictMono node
  node_first : node 0 = source.left
  node_last : node (Fin.last (n + 1)) = source.right

variable {n : ℕ}

def trapNode (i : Fin n) : Fin (n + 2) := i.castSucc.succ

def OrderedMedium.site (D : OrderedMedium n) (i : Fin n) : ℝ := D.node (trapNode i)

def OrderedMedium.gapLength (D : OrderedMedium n) (e : Fin (n + 1)) : ℝ :=
  D.node e.succ - D.node e.castSucc

/-- Every admissible ordered list of physical sites gives this interval model. -/
def OrderedMedium.ofSites (P : SourceInterval) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc P.left P.right)) (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x)
    (s : Fin n → ℝ) (hs : StrictMono s) (hin : ∀ i, s i ∈ Ioo P.left P.right) :
    OrderedMedium n where
  source := P
  conductance := a
  conductance_continuous := ha
  conductance_pos := hapos
  node := Fin.cons P.left (Fin.snoc s P.right)
  node_strictMono := by
    apply Fin.strictMono_cons.mpr
    constructor
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using P.increasing
      · simpa using (hin i).1
    · rw [← Fin.insertNth_last']
      apply (Fin.strictMono_insertNth_iff _ _ _).mpr
      refine ⟨hs, fun i _ => (hin i).2, fun i hi => ?_⟩
      have hnot : ¬ (Fin.last n ≤ i.castSucc) := by
        change ¬ (n ≤ i.val)
        omega
      exact (hnot hi).elim
  node_first := rfl
  node_last := by simp

theorem OrderedMedium.ofSites_site (P : SourceInterval) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc P.left P.right)) (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x)
    (s : Fin n → ℝ) (hs : StrictMono s) (hin : ∀ i, s i ∈ Ioo P.left P.right) (i : Fin n) :
    (OrderedMedium.ofSites P a ha hapos s hs hin).site i = s i := by
  simp [OrderedMedium.site, OrderedMedium.ofSites, trapNode]

theorem OrderedMedium.node_mem (D : OrderedMedium n) (v : Fin (n + 2)) :
    D.node v ∈ Icc D.source.left D.source.right := by
  rw [← D.node_first, ← D.node_last]
  exact ⟨D.node_strictMono.monotone (Fin.zero_le v),
    D.node_strictMono.monotone (Fin.le_last v)⟩

theorem OrderedMedium.site_interior (D : OrderedMedium n) (i : Fin n) :
    D.site i ∈ Ioo D.source.left D.source.right := by
  rw [← D.node_first, ← D.node_last]
  exact ⟨D.node_strictMono (by simp [trapNode]),
    D.node_strictMono (show trapNode i < Fin.last (n + 1) by
      change i.val + 1 < n + 1
      omega)⟩

theorem OrderedMedium.site_strictMono (D : OrderedMedium n) : StrictMono D.site := by
  intro i j hij
  exact D.node_strictMono (by simpa [trapNode] using hij)

theorem OrderedMedium.gapLength_pos (D : OrderedMedium n) (e : Fin (n + 1)) :
    0 < D.gapLength e :=
  sub_pos.mpr (D.node_strictMono Fin.castSucc_lt_succ)

theorem OrderedMedium.gap_point_mem (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc 0 (D.gapLength e)) :
    D.node e.castSucc + x ∈ Icc D.source.left D.source.right := by
  have hl := D.node_mem e.castSucc
  have hr := D.node_mem e.succ
  unfold OrderedMedium.gapLength at hx
  exact ⟨by linarith [hl.1, hx.1], by linarith [hr.2, hx.2]⟩

def OrderedMedium.graph (D : OrderedMedium n) : MetricGraph (Fin (n + 2)) (Fin (n + 1)) where
  tail := Fin.castSucc
  head := Fin.succ
  length := D.gapLength
  length_pos := D.gapLength_pos
  conductance := fun e x => D.conductance (D.node e.castSucc + x)
  source := fun e x => D.source.density (D.node e.castSucc + x)
  conductance_continuous := fun e => D.conductance_continuous.comp
    (continuous_const.add continuous_id).continuousOn (fun _ hx => D.gap_point_mem e hx)
  source_continuous := fun e => D.source.continuous.comp
    (continuous_const.add continuous_id).continuousOn (fun _ hx => D.gap_point_mem e hx)
  conductance_pos := fun e _ hx => D.conductance_pos _ (D.gap_point_mem e hx)
  source_pos := fun e _ hx => D.source.positive _ (D.gap_point_mem e hx)
  connected := path_connected n

/-- Original point strengths, extended by zero to the two reflecting ends. -/
def nodalStrength (κ : Fin n → ℝ) : Fin (n + 2) → ℝ := Fin.cons 0 (Fin.snoc κ 0)

theorem nodalStrength_first (κ : Fin n → ℝ) : nodalStrength κ 0 = 0 := rfl

theorem nodalStrength_last (κ : Fin n → ℝ) : nodalStrength κ (Fin.last (n + 1)) = 0 := by
  simp [nodalStrength]

theorem nodalStrength_trap (κ : Fin n → ℝ) (i : Fin n) :
    nodalStrength κ (trapNode i) = κ i := by
  simp [nodalStrength, trapNode]

theorem nodalStrength_nonneg (κ : Fin n → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ v, 0 ≤ nodalStrength κ v := by
  intro v
  refine Fin.cases (by simp [nodalStrength]) (fun w => ?_) v
  refine Fin.lastCases (by simp [nodalStrength]) (fun i => ?_) w
  simpa [nodalStrength] using hκ i

theorem nodalStrength_anchor (κ : Fin n → ℝ) (hκ : ∃ i, 0 < κ i) :
    ∃ v, 0 < nodalStrength κ v := by
  obtain ⟨i, hi⟩ := hκ
  exact ⟨trapNode i, by simpa only [nodalStrength_trap] using hi⟩

theorem nodalStrength_sum (κ : Fin n → ℝ) : ∑ v, nodalStrength κ v = ∑ i, κ i := by
  rw [Fin.sum_univ_succ]
  simp only [nodalStrength, Fin.cons_zero, Fin.cons_succ, zero_add]
  rw [Fin.sum_univ_castSucc]
  simp

theorem nodalStrength_pairing (κ : Fin n → ℝ) (U : Fin (n + 2) → ℝ) :
    ∑ v, nodalStrength κ v * U v = ∑ i, κ i * U (trapNode i) := by
  rw [Fin.sum_univ_succ]
  simp only [nodalStrength_first, zero_mul, zero_add]
  rw [Fin.sum_univ_castSucc]
  simp [nodalStrength, trapNode]

/-- Weak existence for the actual ordered gaps and original point strengths. -/
theorem OrderedMedium.weak_state_exists (D : OrderedMedium n) (κ : Fin n → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    ∃ U u, WeakGraphEquation D.graph (nodalStrength κ) U u :=
  weak_graph_state_exists D.graph _ (nodalStrength_nonneg κ hκ) (nodalStrength_anchor κ hanchor)

theorem path_flux_first (j₀ j₁ : Fin (n + 1) → ℝ) :
    vertexFlux Fin.castSucc Fin.succ j₀ j₁ (0 : Fin (n + 2)) = j₀ 0 := by
  classical
  simp [vertexFlux, incidenceLoad]

theorem path_flux_last (j₀ j₁ : Fin (n + 1) → ℝ) :
    vertexFlux Fin.castSucc Fin.succ j₀ j₁ (Fin.last (n + 1)) = -j₁ (Fin.last n) := by
  classical
  simp [vertexFlux, incidenceLoad]

theorem path_flux_trap (j₀ j₁ : Fin (n + 1) → ℝ) (i : Fin n) :
    vertexFlux Fin.castSucc Fin.succ j₀ j₁ (trapNode i) = j₀ i.succ - j₁ i.castSucc := by
  classical
  have ht (e : Fin (n + 1)) : e.castSucc = trapNode i ↔ e = i.succ := by
    change e.castSucc = i.succ.castSucc ↔ e = i.succ
    exact Fin.castSucc_inj
  have hh (e : Fin (n + 1)) : e.succ = trapNode i ↔ e = i.castSucc := Fin.succ_inj
  simp only [vertexFlux, incidenceLoad, ht, hh]
  simp [Finset.sum_add_distrib, sub_eq_add_neg]

theorem OrderedMedium.reflecting_endpoints (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    j 0 0 = 0 ∧ j (Fin.last n) (D.gapLength (Fin.last n)) = 0 := by
  have hl := h.vertex_balance 0
  have hr := h.vertex_balance (Fin.last (n + 1))
  change nodalStrength κ 0 * U 0 = vertexFlux Fin.castSucc Fin.succ _ _ 0 at hl
  change nodalStrength κ (Fin.last (n + 1)) * U (Fin.last (n + 1)) =
    vertexFlux Fin.castSucc Fin.succ _ _ (Fin.last (n + 1)) at hr
  rw [nodalStrength_first, zero_mul, path_flux_first] at hl
  rw [nodalStrength_last, zero_mul, path_flux_last] at hr
  change 0 = -j (Fin.last n) (D.gapLength (Fin.last n)) at hr
  constructor <;> linarith

theorem OrderedMedium.flux_jump (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (i : Fin n) :
    j i.succ 0 - j i.castSucc (D.gapLength i.castSucc) = κ i * U (trapNode i) := by
  have hi := h.vertex_balance (trapNode i)
  change nodalStrength κ (trapNode i) * U (trapNode i) =
    vertexFlux Fin.castSucc Fin.succ _ _ (trapNode i) at hi
  rw [nodalStrength_trap, path_flux_trap] at hi
  exact hi.symm

end TimeTraps.Interval
