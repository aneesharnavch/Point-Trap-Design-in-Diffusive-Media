module

public import TimeTraps.Interval.SourceMeanPullbackGeometry
public import TimeTraps.Interval.StateAssembly

@[expose] public section

/-! Pullback of the unit-source state and flux equations through the normalized
source coordinate. The physical flux and point strengths scale by the total
source mass. No derivative of either medium coefficient is used. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

theorem source_mean_edge_pullback {a b ρ φ u j : ℝ → ℝ} {L R S : ℝ}
    (hS : S ≠ 0)
    (ha : ∀ t ∈ Ioo 0 L, a t ≠ 0) (hρ : ∀ t ∈ Ioo 0 L, ρ t ≠ 0)
    (hc : ContinuousOn φ (Icc 0 L))
    (hcc : MapsTo φ (Icc 0 L) (Icc 0 R))
    (hoo : MapsTo φ (Ioo 0 L) (Ioo 0 R))
    (hd : ∀ t ∈ Ioo 0 L, HasDerivAt φ (ρ t / S) t)
    (hb : ∀ t ∈ Ioo 0 L, b (φ t) = a t * ρ t / S ^ 2)
    (h : EdgeEquation b (fun _ => 1) 0 R u j) :
    EdgeEquation a ρ 0 L (fun t => u (φ t)) (fun t => S * j (φ t)) := by
  refine ⟨h.state_continuous.comp hc hcc,
    continuousOn_const.mul (h.flux_continuous.comp hc hcc), ?_, ?_⟩
  · intro t ht
    have hu := (h.state_derivative (φ t) (hoo ht)).comp t (hd t ht)
    convert! hu using 1
    rw [hb t ht]
    field_simp [hS, ha t ht, hρ t ht]
  · intro t ht
    have hj := ((h.flux_derivative (φ t) (hoo ht)).comp t (hd t ht)).const_mul S
    convert! hj using 1
    field_simp [hS]

theorem source_mean_vertexFlux_scale {V E : Type*} [Fintype E]
    (tail head : E → V) (j₀ j₁ : E → ℝ) (S : ℝ) (v : V) :
    vertexFlux tail head (fun e => S * j₀ e) (fun e => S * j₁ e) v =
      S * vertexFlux tail head j₀ j₁ v := by
  classical
  unfold vertexFlux incidenceLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem source_mean_nodalStrength_scale {n : ℕ} (κ : Fin n → ℝ) (S : ℝ)
    (v : Fin (n + 2)) :
    nodalStrength (fun i => S * κ i) v = S * nodalStrength κ v := by
  refine Fin.cases ?_ (fun i => ?_) v
  · simp only [nodalStrength_first, mul_zero]
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · change nodalStrength _ (Fin.last (n + 1)) = S * nodalStrength _ (Fin.last (n + 1))
      simp only [nodalStrength_last, mul_zero]
    · change nodalStrength _ (trapNode i) = S * nodalStrength κ (trapNode i)
      rw [nodalStrength_trap, nodalStrength_trap]

variable {n : ℕ} (A : IntervalMedium) (D : OrderedMedium n)
  (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source)

noncomputable def sourceMeanPullbackEdgeState (u : Fin (n + 1) → ℝ → ℝ)
    (e : Fin (n + 1)) (t : ℝ) : ℝ :=
  u e (sourceMeanGapCoordinate A D hD e t)

noncomputable def sourceMeanPullbackFlux (j : Fin (n + 1) → ℝ → ℝ)
    (e : Fin (n + 1)) (t : ℝ) : ℝ :=
  A.source.mass * j e (sourceMeanGapCoordinate A D hD e t)

theorem sourceMeanPullback_edge_equation
    (haD : D.conductance = sourceMeanConductance A)
    {u j : Fin (n + 1) → ℝ → ℝ} (e : Fin (n + 1))
    (h : EdgeEquation (D.graph.conductance e) (D.graph.source e)
      0 (D.gapLength e) (u e) (j e)) :
    EdgeEquation ((sourceMeanPullbackGeometry A D hD).graph.conductance e)
      ((sourceMeanPullbackGeometry A D hD).graph.source e)
      0 ((sourceMeanPullbackGeometry A D hD).gapLength e)
      (sourceMeanPullbackEdgeState A D hD u e) (sourceMeanPullbackFlux A D hD j e) := by
  let G := sourceMeanPullbackGeometry A D hD
  have hf : D.graph.source e = fun _ => 1 := by
    funext t
    change D.source.density (D.node e.castSucc + t) = 1
    rw [hD]
    rfl
  rw [hf] at h
  exact source_mean_edge_pullback
    (a := G.graph.conductance e) (b := D.graph.conductance e)
    (ρ := G.graph.source e) (φ := sourceMeanGapCoordinate A D hD e) (u := u e) (j := j e)
    (ne_of_gt A.source.mass_pos)
    (fun t ht => ne_of_gt (G.graph.conductance_pos e t (Ioo_subset_Icc_self ht)))
    (fun t ht => ne_of_gt (G.graph.source_pos e t (Ioo_subset_Icc_self ht)))
    (sourceMeanGapCoordinate_continuous A D hD e)
    (fun _ ht => sourceMeanGapCoordinate_mem A D hD e ht)
    (fun _ ht => sourceMeanGapCoordinate_interior A D hD e ht)
    (fun _ ht => sourceMeanGapCoordinate_derivative A D hD e ht)
    (fun _ ht => sourceMeanGapCoordinate_conductance A D hD haD e (Ioo_subset_Icc_self ht)) h

theorem sourceMeanPullback_graph_equation
    (haD : D.conductance = sourceMeanConductance A)
    {κ : Fin n → ℝ} {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    GraphEquation (sourceMeanPullbackGeometry A D hD).graph
      (nodalStrength (fun i => A.source.mass * κ i)) U
      (sourceMeanPullbackEdgeState A D hD u) (sourceMeanPullbackFlux A D hD j) := by
  refine ⟨fun e => sourceMeanPullback_edge_equation A D hD haD e (h.edge_equation e),
    ?_, ?_, ?_⟩
  · intro e
    change u e (sourceMeanGapCoordinate A D hD e 0) = U e.castSucc
    rw [sourceMeanGapCoordinate_tail]
    exact h.tail_value e
  · intro e
    change u e (sourceMeanGapCoordinate A D hD e
      ((sourceMeanPullbackGeometry A D hD).gapLength e)) = U e.succ
    rw [sourceMeanGapCoordinate_head]
    exact h.head_value e
  · intro v
    change nodalStrength _ v * U v = vertexFlux Fin.castSucc Fin.succ
      (fun e => A.source.mass * j e (sourceMeanGapCoordinate A D hD e 0))
      (fun e => A.source.mass * j e (sourceMeanGapCoordinate A D hD e
        ((sourceMeanPullbackGeometry A D hD).gapLength e))) v
    simp only [sourceMeanGapCoordinate_tail, sourceMeanGapCoordinate_head]
    rw [source_mean_vertexFlux_scale, source_mean_nodalStrength_scale, mul_assoc,
      h.vertex_balance v]
    rfl

theorem sourceMeanPullback_weak_equation
    (haD : D.conductance = sourceMeanConductance A)
    {κ : Fin n → ℝ} {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    WeakIntervalEquation (sourceMeanPullbackGeometry A D hD)
      (fun i => A.source.mass * κ i)
      ((sourceMeanPullbackGeometry A D hD).assembledState U
        (sourceMeanPullbackEdgeState A D hD u)) :=
  (sourceMeanPullbackGeometry A D hD).assembledState_weak
    (sourceMeanPullback_graph_equation A D hD haD h)

end TimeTraps.Interval
