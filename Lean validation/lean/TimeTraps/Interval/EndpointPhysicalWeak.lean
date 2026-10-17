module

public import TimeTraps.Interval.EndpointPhysicalData
public import TimeTraps.Interval.GeneralEnergyAssembly

@[expose] public section

/-!
The independent physical weak equation with reactive endpoints. The state
and every test belong to the full interval H1 space. Existence is obtained
by gluing the actual graph solution; uniqueness follows by testing the
difference, including every active endpoint penalty.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

structure EndpointWeakEquation (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) (w : ℝ → ℝ) : Prop where
  energy : IntervalEnergy w D.source.left D.source.right
  weak_form : ∀ v, IntervalEnergy v D.source.left D.source.right →
    (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv v x) +
      (∑ k, R.nodal k * w (D.node k) * v (D.node k)) =
        ∫ x in D.source.left..D.source.right, D.source.density x * v x

theorem EndpointWeakEquation.expanded_weak_form {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (v : ℝ → ℝ) (hv : IntervalEnergy v D.source.left D.source.right) :
    (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv v x) +
      (R.leftStrength * w D.source.left * v D.source.left +
        (∑ i, R.interiorStrength i * w (D.site i) * v (D.site i)) +
        R.rightStrength * w D.source.right * v D.source.right) =
      ∫ x in D.source.left..D.source.right, D.source.density x * v x := by
  have h := hw.weak_form v hv
  simp_rw [mul_assoc] at h
  rw [R.nodal_pairing] at h
  simpa only [D.node_first, D.node_last, OrderedMedium.site, mul_assoc] using h

theorem EndpointWeakEquation.congr_state {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w z : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (heq : EqOn w z (Icc D.source.left D.source.right)) : EndpointWeakEquation D R z := by
  refine ⟨hw.energy.congr (by simpa only [uIcc_of_le D.source.increasing.le] using heq), ?_⟩
  intro v hv
  have hd := (heq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hi : (∫ x in D.source.left..D.source.right, D.conductance x * deriv z x * deriv v x) =
      ∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv v x := by
    apply intervalIntegral.integral_congr_Ioo_of_le D.source.increasing.le
    intro x hx
    dsimp only
    rw [hd hx]
  have hs : (∑ k, R.nodal k * z (D.node k) * v (D.node k)) =
      ∑ k, R.nodal k * w (D.node k) * v (D.node k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [heq (D.node_mem k)]
  rw [hi, hs]
  exact hw.weak_form v hv

theorem OrderedMedium.assembledState_endpointWeak (D : OrderedMedium A.interiorCount)
    {R : EndpointReactions A K} {U : Fin (A.interiorCount + 2) → ℝ}
    {u j : Fin (A.interiorCount + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph R.nodal U u j) :
    EndpointWeakEquation D R (D.assembledState U u) := by
  have henergy := D.assembledState_energy_general h.energy_membership
  refine ⟨henergy, ?_⟩
  intro v hv
  have ht := h.to_weak.weak_form (fun k => v (D.node k)) (D.gapRestriction v) (D.restrict_energy hv)
  have ha : ContinuousOn D.conductance (uIcc D.source.left D.source.right) := by
    simpa only [uIcc_of_le D.source.increasing.le] using D.conductance_continuous
  have he : (∑ e, ∫ x in 0..D.graph.length e,
      D.graph.conductance e x * deriv (u e) x * deriv (D.gapRestriction v e) x) =
      ∫ x in D.source.left..D.source.right,
        D.conductance x * deriv (D.assembledState U u) x * deriv v x := by
    rw [← D.integral_gap_sum (henergy.bilinear_integrable hv ha)]
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr_Ioo_of_le (D.gapLength_pos e).le
    intro x hx
    change D.conductance (D.node e.castSucc + x) * deriv (u e) x *
      deriv (D.gapRestriction v e) x = _
    dsimp only
    rw [D.gapRestriction_deriv, D.assembledState_gap_deriv h.energy_membership e hx]
  have hs : (∑ e, ∫ x in 0..D.graph.length e, D.graph.source e x * D.gapRestriction v e x) =
      ∫ x in D.source.left..D.source.right, D.source.density x * v x :=
    D.integral_gap_sum (D.source_test_integrable hv)
  have hn : (∑ k, R.nodal k * U k * v (D.node k)) =
      ∑ k, R.nodal k * D.assembledState U u (D.node k) * v (D.node k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [D.assembledState_node h.energy_membership]
  rwa [he, hs, hn] at ht

theorem endpoint_weak_state_exists (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) : ∃ w, EndpointWeakEquation D R w := by
  obtain ⟨U, u, j, h⟩ := graph_state_exists D.graph R.nodal R.nodal_nonneg R.nodal_anchor
  exact ⟨D.assembledState U u, D.assembledState_endpointWeak h⟩

theorem EndpointWeakEquation.difference_energy_zero {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w z : ℝ → ℝ}
    (hw : EndpointWeakEquation D R w) (hz : EndpointWeakEquation D R z) :
    (∫ x in D.source.left..D.source.right,
      D.conductance x * deriv (fun y => w y - z y) x ^ 2) +
      (∑ k, R.nodal k * (w (D.node k) - z (D.node k)) ^ 2) = 0 := by
  let δ : ℝ → ℝ := fun x => w x - z x
  have hδ := hw.energy.sub hz.energy
  have h₁ := hw.weak_form δ hδ
  have h₂ := hz.weak_form δ hδ
  have ha : ContinuousOn D.conductance (uIcc D.source.left D.source.right) := by
    simpa only [uIcc_of_le D.source.increasing.le] using D.conductance_continuous
  have he : (∫ x in D.source.left..D.source.right, D.conductance x * deriv δ x ^ 2) =
      (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv δ x) -
      (∫ x in D.source.left..D.source.right, D.conductance x * deriv z x * deriv δ x) := by
    simpa only [δ, pow_two, mul_assoc] using hw.energy.bilinear_sub_left hz.energy hδ ha
  have hs : (∑ k, R.nodal k * δ (D.node k) ^ 2) =
      (∑ k, R.nodal k * w (D.node k) * δ (D.node k)) -
      (∑ k, R.nodal k * z (D.node k) * δ (D.node k)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [δ]
    ring
  change (∫ x in D.source.left..D.source.right, D.conductance x * deriv δ x ^ 2) +
    (∑ k, R.nodal k * δ (D.node k) ^ 2) = 0
  rw [he, hs]
  linarith

theorem EndpointReactions.energy_zero (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) {w : ℝ → ℝ}
    (hw : IntervalEnergy w D.source.left D.source.right)
    (hzero : (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2) +
      (∑ k, R.nodal k * w (D.node k) ^ 2) = 0) :
    ∀ x ∈ Icc D.source.left D.source.right, w x = 0 := by
  have he : 0 ≤ ∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2 :=
    intervalIntegral.integral_nonneg D.source.increasing.le
      (fun x hx => mul_nonneg (D.conductance_pos x hx).le (sq_nonneg _))
  have hr : ∀ k, 0 ≤ R.nodal k * w (D.node k) ^ 2 :=
    fun k => mul_nonneg (R.nodal_nonneg k) (sq_nonneg _)
  have hs := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => hr k)
  have hEz : (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2) = 0 := by
    linarith
  have hRz : (∑ k, R.nodal k * w (D.node k) ^ 2) = 0 := by linarith
  have hc := hw.constant_of_energy_zero D.source.increasing.le
    D.conductance_continuous D.conductance_pos hEz
  obtain ⟨k, hk⟩ := R.nodal_anchor
  have hk₀ := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hr v)).mp hRz k (Finset.mem_univ k)
  have hw₀ : w (D.node k) = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp hk₀).resolve_left (ne_of_gt hk))
  intro x hx
  exact (hc x hx).trans ((hc _ (D.node_mem k)).symm.trans hw₀)

theorem endpoint_weak_state_unique {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w z : ℝ → ℝ}
    (hw : EndpointWeakEquation D R w) (hz : EndpointWeakEquation D R z) :
    EqOn w z (Icc D.source.left D.source.right) := by
  have he := R.energy_zero D (hw.energy.sub hz.energy) (hw.difference_energy_zero hz)
  intro x hx
  exact sub_eq_zero.mp (he x hx)

end TimeTraps.Interval
