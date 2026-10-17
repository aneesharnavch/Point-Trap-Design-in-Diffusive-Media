module

public import TimeTraps.Interval.HomogeneousPoissonShooting
public import TimeTraps.Interval.HomogeneousMeanDeficit
public import TimeTraps.Graph.ConstantEdge

@[expose] public section

/-!
The affine shooting solver reconstructs the actual full-H1 weak solution for
arbitrary ordered positive interior reactions in a homogeneous medium.
Every closed gap has the computed quadratic profile. Exact integration of
those pieces, including the final gap without a trap update, gives its mean.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {G : OrderedMedium n} {D : ℝ} {κ : Fin n → ℝ} {w : ℝ → ℝ}
  {j : Fin (n + 1) → ℝ → ℝ}

theorem homogeneous_poisson_gap_of_graph
    (h : GraphEquation G.graph (nodalStrength κ) (fun v => w (G.node v)) (G.gapRestriction w) j)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (e : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc 0 (G.gapLength e)) :
    poissonGap D t (w (G.node e.castSucc), j e 0 / D) =
      (w (G.node e.castSucc + t), j e t / D) := by
  have he : EdgeEquation (fun _ => D) (fun _ => 1) 0 (G.gapLength e)
      (G.gapRestriction w e) (j e) := by
    have he := h.edge_equation e
    change EdgeEquation (fun x => G.conductance (G.node e.castSucc + x))
      (fun x => G.source.density (G.node e.castSucc + x)) 0 (G.gapLength e)
      (G.gapRestriction w e) (j e) at he
    simpa only [ha, hρ] using he
  have hu := constant_edge_state he ht
  have hj := constant_edge_flux he ht
  simp only [OrderedMedium.gapRestriction, add_zero] at hu
  apply Prod.ext
  · change w (G.node e.castSucc) + (j e 0 / D) * t - t ^ 2 / (2 * D) = _
    rw [hu]
    ring
  · change j e 0 / D - t / D = j e t / D
    rw [hj]
    ring

theorem homogeneous_poisson_run_of_graph
    (h : GraphEquation G.graph (nodalStrength κ) (fun v => w (G.node v)) (G.gapRestriction w) j)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (e : Fin (n + 1)) :
    poissonRun D G.gapLength κ (w G.source.left) e = (w (G.node e.castSucc), j e 0 / D) := by
  induction e using Fin.induction with
  | zero =>
    rw [poissonRun_zero, Fin.castSucc_zero, G.node_first, (G.reflecting_endpoints h).1]
    simp only [zero_div]
  | succ i ih =>
    rw [poissonRun_succ, ih,
      homogeneous_poisson_gap_of_graph h ha hρ i.castSucc ⟨(G.gapLength_pos i.castSucc).le, le_rfl⟩]
    have hj := G.flux_jump h i
    change j i.succ 0 - j i.castSucc (G.gapLength i.castSucc) = κ i * w (G.site i) at hj
    simp only [OrderedMedium.gapLength, add_sub_cancel]
    apply Prod.ext
    · rfl
    · change j i.castSucc (G.gapLength i.castSucc) / D +
        κ i * w (G.site i) / D = j i.succ 0 / D
      rw [← hj]
      ring

theorem homogeneous_poisson_terminal_of_graph
    (h : GraphEquation G.graph (nodalStrength κ) (fun v => w (G.node v)) (G.gapRestriction w) j)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1) :
    poissonTerminal D G.gapLength κ (w G.source.left) = (w G.source.right, 0) := by
  rw [poissonTerminal, homogeneous_poisson_run_of_graph h ha hρ,
    homogeneous_poisson_gap_of_graph h ha hρ (Fin.last n)
      ⟨(G.gapLength_pos (Fin.last n)).le, le_rfl⟩,
    (G.reflecting_endpoints h).2]
  simp only [OrderedMedium.gapLength, add_sub_cancel, zero_div]
  change (w (G.node (Fin.last (n + 1))), 0) = _
  rw [G.node_last]

theorem homogeneous_poisson_initial_of_graph
    (h : GraphEquation G.graph (nodalStrength κ) (fun v => w (G.node v)) (G.gapRestriction w) j)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    w G.source.left = poissonInitial D G.gapLength κ := by
  apply (poissonTerminal_reflecting_iff D G.gapLength κ hD
    (fun e => (G.gapLength_pos e).le) hκ hn _).mp
  rw [homogeneous_poisson_terminal_of_graph h ha hρ]

theorem homogeneous_poisson_profile_of_graph
    (h : GraphEquation G.graph (nodalStrength κ) (fun v => w (G.node v)) (G.gapRestriction w) j)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n)
    (e : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc 0 (G.gapLength e)) :
    w (G.node e.castSucc + t) =
      (poissonGap D t (poissonRun D G.gapLength κ (poissonInitial D G.gapLength κ) e)).1 := by
  rw [← homogeneous_poisson_initial_of_graph h ha hρ hD hκ hn,
    homogeneous_poisson_run_of_graph h ha hρ, homogeneous_poisson_gap_of_graph h ha hρ e ht]

noncomputable def OrderedMedium.poissonState (G : OrderedMedium n) (D : ℝ) (κ : Fin n → ℝ)
    (x : ℝ) : ℝ :=
  poissonInitial D G.gapLength κ + ∑ e : Fin (n + 1),
    ((poissonGap D (G.gapProjection e x)
      (poissonRun D G.gapLength κ (poissonInitial D G.gapLength κ) e)).1 -
      (poissonRun D G.gapLength κ (poissonInitial D G.gapLength κ) e).1)

theorem homogeneous_poisson_state_of_graph
    (h : GraphEquation G.graph (nodalStrength κ) (fun v => w (G.node v)) (G.gapRestriction w) j)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    EqOn (G.poissonState D κ) w (Icc G.source.left G.source.right) := by
  intro x hx
  calc
    G.poissonState D κ x = G.assembledState (fun v => w (G.node v)) (G.gapRestriction w) x := by
      unfold OrderedMedium.poissonState OrderedMedium.assembledState
      dsimp only
      rw [← homogeneous_poisson_initial_of_graph h ha hρ hD hκ hn, G.node_first]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      rw [homogeneous_poisson_run_of_graph h ha hρ,
        homogeneous_poisson_gap_of_graph h ha hρ e (G.gapProjection_mem e x)]
      rfl
    _ = w x := G.assembledRestriction_eq (G.weak_of_strong h).energy hx

theorem WeakIntervalEquation.homogeneous_poisson_state (h : WeakIntervalEquation G κ w)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    EqOn (G.poissonState D κ) w (Icc G.source.left G.source.right) := by
  obtain ⟨j, hj⟩ := h.to_strong (fun i => (hκ i).le) ⟨⟨0, hn⟩, hκ ⟨0, hn⟩⟩
  exact homogeneous_poisson_state_of_graph hj ha hρ hD hκ hn

theorem OrderedMedium.poissonState_weak (G : OrderedMedium n) (D : ℝ) (κ : Fin n → ℝ)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    WeakIntervalEquation G κ (G.poissonState D κ) := by
  obtain ⟨w, hw⟩ := interval_weak_state_exists G κ (fun i => (hκ i).le)
    ⟨⟨0, hn⟩, hκ ⟨0, hn⟩⟩
  exact hw.congr_state (hw.homogeneous_poisson_state ha hρ hD hκ hn).symm

theorem OrderedMedium.poissonState_energy (G : OrderedMedium n) (D : ℝ) (κ : Fin n → ℝ)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    IntervalEnergy (G.poissonState D κ) G.source.left G.source.right :=
  (G.poissonState_weak D κ ha hρ hD hκ hn).energy

theorem OrderedMedium.poissonState_unique (G : OrderedMedium n) (D : ℝ) (κ : Fin n → ℝ)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n)
    {w : ℝ → ℝ} (hw : WeakIntervalEquation G κ w) :
    EqOn w (G.poissonState D κ) (Icc G.source.left G.source.right) :=
  interval_weak_state_unique hw (G.poissonState_weak D κ ha hρ hD hκ hn)
    (fun i => (hκ i).le) ⟨⟨0, hn⟩, hκ ⟨0, hn⟩⟩

theorem poissonGap_integral (D h : ℝ) (s : ℝ × ℝ) :
    (∫ t in (0 : ℝ)..h, (poissonGap D t s).1) =
      s.1 * h + s.2 * h ^ 2 / 2 - h ^ 3 / (6 * D) := by
  have hd (t : ℝ) : HasDerivAt
      (fun x : ℝ => s.1 * x + s.2 * x ^ 2 / 2 - x ^ 3 / (6 * D))
      (poissonGap D t s).1 t := by
    convert (((hasDerivAt_id t).const_mul s.1).add
      ((((hasDerivAt_id t).pow 2).const_mul s.2).div_const 2)).sub
      (((hasDerivAt_id t).pow 3).div_const (6 * D)) using 1 <;>
      first | rfl | (simp only [poissonGap, id_eq]; ring)
  have hc : Continuous (fun t => (poissonGap D t s).1) :=
    (continuous_const.add (continuous_const.mul continuous_id)).sub
      ((continuous_id.pow 2).div_const (2 * D))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 h)]
  ring

theorem WeakIntervalEquation.homogeneous_poisson_integral (h : WeakIntervalEquation G κ w)
    (ha : G.conductance = fun _ => D) (hρ : G.source.density = fun _ => 1)
    (hD : 0 < D) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    (∫ x in G.source.left..G.source.right, w x) =
      ∑ e : Fin (n + 1),
        ((poissonRun D G.gapLength κ (poissonInitial D G.gapLength κ) e).1 * G.gapLength e +
        (poissonRun D G.gapLength κ (poissonInitial D G.gapLength κ) e).2 * G.gapLength e ^ 2 / 2 -
        G.gapLength e ^ 3 / (6 * D)) := by
  obtain ⟨j, hj⟩ := h.to_strong (fun i => (hκ i).le) ⟨⟨0, hn⟩, hκ ⟨0, hn⟩⟩
  rw [← G.integral_gap_sum h.energy.continuousOn.intervalIntegrable]
  apply Finset.sum_congr rfl
  intro e _
  calc
    _ = ∫ t in (0 : ℝ)..G.gapLength e,
        (poissonGap D t (poissonRun D G.gapLength κ (poissonInitial D G.gapLength κ) e)).1 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (G.gapLength_pos e).le
      intro t ht
      exact homogeneous_poisson_profile_of_graph hj ha hρ hD hκ hn e (Ioo_subset_Icc_self ht)
    _ = _ := poissonGap_integral D (G.gapLength e) _

theorem IntervalDesign.homogeneous_poisson_state {L K : ℝ} {hL : 0 < L} {hD : 0 < D}
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    EqOn (E.geometry.poissonState D E.strength) E.state (Icc (0 : ℝ) L) := by
  have hρ : E.geometry.source.density = fun _ => 1 := by rw [E.homogeneous_source]; rfl
  have he := E.equation.homogeneous_poisson_state E.homogeneous_conductance hρ
    hD E.strength_pos E.partition.size_pos
  rw [E.homogeneous_source] at he
  exact he

theorem IntervalDesign.homogeneous_poisson_mean {L K : ℝ} {hL : 0 < L} {hD : 0 < D}
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.meanCost = (∑ e : Fin (n + 1),
      ((poissonRun D E.geometry.gapLength E.strength
        (poissonInitial D E.geometry.gapLength E.strength) e).1 * E.geometry.gapLength e +
      (poissonRun D E.geometry.gapLength E.strength
        (poissonInitial D E.geometry.gapLength E.strength) e).2 * E.geometry.gapLength e ^ 2 / 2 -
      E.geometry.gapLength e ^ 3 / (6 * D))) / L := by
  have hρ : E.geometry.source.density = fun _ => 1 := by rw [E.homogeneous_source]; rfl
  have he := E.equation.homogeneous_poisson_integral E.homogeneous_conductance hρ
    hD E.strength_pos E.partition.size_pos
  rw [E.homogeneous_source] at he
  change (∫ x in (0 : ℝ)..L, E.state x) = _ at he
  rw [E.homogeneous_meanCost, he]

end TimeTraps.Interval
