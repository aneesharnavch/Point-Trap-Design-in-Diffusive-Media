module

public import TimeTraps.Spectral.NetworkDirichlet
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Exact polarization, zero-energy kernel equations, and strict positivity by
incidence connectivity. No spectral existence is assumed here. -/

namespace TimeTraps.Spectral

open Set Filter TimeTraps.Graph
open scoped BigOperators Topology Classical

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def SpectralNetwork.nodalPairing (P : SpectralNetwork V E)
    (k : ℝ) (U W : V → ℝ) : ℝ :=
  (∑ e, P.edgeWeight k e * (Real.cos (k * P.length e) *
    (U (P.tail e) * W (P.tail e) + U (P.head e) * W (P.head e)) -
      U (P.tail e) * W (P.head e) - U (P.head e) * W (P.tail e))) +
        ∑ v, P.strength v * U v * W v

theorem SpectralNetwork.nodalPairing_operator (P : SpectralNetwork V E)
    (k : ℝ) (U W : V → ℝ) : P.nodalPairing k U W = ∑ v, W v * P.nodalOperator k U v := by
  have he : (∑ e, P.edgeWeight k e * (Real.cos (k * P.length e) *
      (U (P.tail e) * W (P.tail e) + U (P.head e) * W (P.head e)) -
        U (P.tail e) * W (P.head e) - U (P.head e) * W (P.tail e))) =
      ∑ e, (P.rightEndpointFlux k U e * W (P.head e) -
        P.leftEndpointFlux k U e * W (P.tail e)) := by
    apply Finset.sum_congr rfl
    intro e _
    unfold leftEndpointFlux rightEndpointFlux
    ring
  unfold nodalPairing nodalOperator
  rw [he, incidence_boundary_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ v, P.strength v * U v * W v) = ∑ v, W v * (P.strength v * U v) := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hs]
  ring

theorem SpectralNetwork.nodalForm_variation (P : SpectralNetwork V E)
    (k t : ℝ) (U W : V → ℝ) :
    P.nodalForm k (fun v => U v + t * W v) = P.nodalForm k U +
      2 * t * P.nodalPairing k U W + t ^ 2 * P.nodalForm k W := by
  unfold nodalForm nodalPairing
  rw [mul_add, mul_add]
  simp only [Finset.mul_sum]
  have he : (∑ e, P.edgeWeight k e * (Real.cos (k * P.length e) *
      ((U (P.tail e) + t * W (P.tail e)) ^ 2 + (U (P.head e) + t * W (P.head e)) ^ 2) -
        2 * (U (P.tail e) + t * W (P.tail e)) * (U (P.head e) + t * W (P.head e)))) =
      (∑ e, P.edgeWeight k e * (Real.cos (k * P.length e) *
        (U (P.tail e) ^ 2 + U (P.head e) ^ 2) - 2 * U (P.tail e) * U (P.head e))) +
      (∑ e, 2 * t * (P.edgeWeight k e * (Real.cos (k * P.length e) *
        (U (P.tail e) * W (P.tail e) + U (P.head e) * W (P.head e)) -
          U (P.tail e) * W (P.head e) - U (P.head e) * W (P.tail e)))) +
      (∑ e, t ^ 2 * (P.edgeWeight k e * (Real.cos (k * P.length e) *
        (W (P.tail e) ^ 2 + W (P.head e) ^ 2) - 2 * W (P.tail e) * W (P.head e)))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hv : (∑ v, P.strength v * (U v + t * W v) ^ 2) =
      (∑ v, P.strength v * U v ^ 2) + (∑ v, 2 * t * (P.strength v * U v * W v)) +
        ∑ v, t ^ 2 * (P.strength v * W v ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he, hv]
  ring

theorem SpectralNetwork.pairing_zero_of_nodalForm_zero (P : SpectralNetwork V E)
    (k : ℝ) {U : V → ℝ} (hpos : ∀ W, 0 ≤ P.nodalForm k W)
    (hzero : P.nodalForm k U = 0) (W : V → ℝ) : P.nodalPairing k U W = 0 := by
  let f := fun t : ℝ => 2 * t * P.nodalPairing k U W + t ^ 2 * P.nodalForm k W
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hpos (fun v => U v + t * W v)
    rw [P.nodalForm_variation, hzero, zero_add] at h
    simpa only [f, mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] using h
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (P.nodalPairing k U W)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (P.nodalForm k W))
  have hz := hmin.hasDerivAt_eq_zero hd
  norm_num at hz
  linarith

theorem SpectralNetwork.nodalOperator_zero_of_nodalForm_zero (P : SpectralNetwork V E)
    (k : ℝ) {U : V → ℝ} (hpos : ∀ W, 0 ≤ P.nodalForm k W)
    (hzero : P.nodalForm k U = 0) : ∀ v, P.nodalOperator k U v = 0 := by
  classical
  intro v
  have h := P.pairing_zero_of_nodalForm_zero k hpos hzero (fun w => if w = v then 1 else 0)
  rw [P.nodalPairing_operator] at h
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

omit [Fintype V] in
theorem SpectralNetwork.nodalOperator_at_zero (P : SpectralNetwork V E)
    (k : ℝ) {U : V → ℝ} {v : V} (hv : U v = 0) :
    P.nodalOperator k U v = -∑ e,
      ((if P.tail e = v then P.edgeWeight k e * U (P.head e) else 0) +
        (if P.head e = v then P.edgeWeight k e * U (P.tail e) else 0)) := by
  classical
  unfold nodalOperator vertexFlux incidenceLoad
  rw [hv, mul_zero, zero_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  unfold leftEndpointFlux rightEndpointFlux
  split_ifs <;> simp_all

omit [Fintype V] in
theorem SpectralNetwork.nodal_zero_edge_iff (P : SpectralNetwork V E) {k : ℝ}
    (hk : P.BelowFirstPole k) {U : V → ℝ} (hU : ∀ v, 0 ≤ U v)
    (hop : ∀ v, P.nodalOperator k U v = 0) (e : E) :
    U (P.tail e) = 0 ↔ U (P.head e) = 0 := by
  classical
  have hterms (v : V) : ∀ d : E,
      0 ≤ (if P.tail d = v then P.edgeWeight k d * U (P.head d) else 0) ∧
      0 ≤ (if P.head d = v then P.edgeWeight k d * U (P.tail d) else 0) := by
    intro d
    constructor <;> split_ifs <;>
      first | exact mul_nonneg (P.edgeWeight_pos hk d).le (hU _) | exact le_rfl
  have hrow (v : V) (hv : U v = 0) (d : E) :
      (if P.tail d = v then P.edgeWeight k d * U (P.head d) else 0) = 0 ∧
      (if P.head d = v then P.edgeWeight k d * U (P.tail d) else 0) = 0 := by
    have hz := hop v
    rw [P.nodalOperator_at_zero k hv, neg_eq_zero] at hz
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => add_nonneg (hterms v d).1 (hterms v d).2)).mp hz d (Finset.mem_univ d)
    exact (add_eq_zero_iff_of_nonneg (hterms v d).1 (hterms v d).2).mp he
  constructor
  · intro hz
    have h := (hrow (P.tail e) hz e).1
    simp only [ite_true] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (P.edgeWeight_pos hk e))
  · intro hz
    have h := (hrow (P.head e) hz e).2
    simp only [ite_true] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (P.edgeWeight_pos hk e))

omit [Fintype V] in
theorem SpectralNetwork.nonnegative_nodal_kernel_positive (P : SpectralNetwork V E) {k : ℝ}
    (hk : P.BelowFirstPole k) {U : V → ℝ} (hU : ∀ v, 0 ≤ U v) (hne : U ≠ 0)
    (hop : ∀ v, P.nodalOperator k U v = 0) : ∀ v, 0 < U v := by
  have hprop (v w : V) : U v = 0 ↔ U w = 0 := by
    induction P.connected v w with
    | rel v w h =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact P.nodal_zero_edge_iff hk hU hop e
    | refl v => exact Iff.rfl
    | symm v w _ ih => exact ih.symm
    | trans v w z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  intro v
  by_contra h
  have hz : U v = 0 := le_antisymm (le_of_not_gt h) (hU v)
  apply hne
  funext w
  exact (hprop v w).mp hz

end TimeTraps.Spectral
