module

public import TimeTraps.Spectral.NetworkProblem
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

@[expose] public section

/-! Exact finite endpoint form for sinusoidal network edges, continuously extended
to zero wavenumber. It is derived independently of a principal eigenvalue. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Graph
open scoped BigOperators Topology

variable {V E : Type*}

def SpectralNetwork.BelowFirstPole (P : SpectralNetwork V E) (k : ℝ) : Prop :=
  0 ≤ k ∧ ∀ e, k * P.length e < Real.pi

noncomputable def SpectralNetwork.edgeWeight (P : SpectralNetwork V E) (k : ℝ) (e : E) : ℝ :=
  (P.diffusivity / P.length e) / Real.sinc (k * P.length e)

noncomputable def SpectralNetwork.nodalForm [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) (k : ℝ) (U : V → ℝ) : ℝ :=
  (∑ e, P.edgeWeight k e * (Real.cos (k * P.length e) *
    (U (P.tail e) ^ 2 + U (P.head e) ^ 2) - 2 * U (P.tail e) * U (P.head e))) +
      ∑ v, P.strength v * U v ^ 2

noncomputable def SpectralNetwork.leftEndpointFlux (P : SpectralNetwork V E)
    (k : ℝ) (U : V → ℝ) (e : E) : ℝ :=
  P.edgeWeight k e * (U (P.head e) - Real.cos (k * P.length e) * U (P.tail e))

noncomputable def SpectralNetwork.rightEndpointFlux (P : SpectralNetwork V E)
    (k : ℝ) (U : V → ℝ) (e : E) : ℝ :=
  P.edgeWeight k e * (Real.cos (k * P.length e) * U (P.head e) - U (P.tail e))

noncomputable def SpectralNetwork.nodalOperator [Fintype E]
    (P : SpectralNetwork V E) (k : ℝ) (U : V → ℝ) (v : V) : ℝ :=
  P.strength v * U v - vertexFlux P.tail P.head
    (P.leftEndpointFlux k U) (P.rightEndpointFlux k U) v

theorem SpectralNetwork.zero_belowFirstPole (P : SpectralNetwork V E) : P.BelowFirstPole 0 :=
  ⟨le_rfl, fun _ => by simpa only [zero_mul] using Real.pi_pos⟩

theorem SpectralNetwork.sinc_pos (P : SpectralNetwork V E) {k : ℝ}
    (hk : P.BelowFirstPole k) (e : E) : 0 < Real.sinc (k * P.length e) := by
  rcases eq_or_lt_of_le hk.1 with h | h
  · rw [← h, zero_mul, Real.sinc_zero]
    exact zero_lt_one
  · have hp := mul_pos h (P.length_pos e)
    rw [Real.sinc_of_ne_zero (ne_of_gt hp)]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hp (hk.2 e)) hp

theorem SpectralNetwork.edgeWeight_pos (P : SpectralNetwork V E) {k : ℝ}
    (hk : P.BelowFirstPole k) (e : E) : 0 < P.edgeWeight k e :=
  div_pos (div_pos P.diffusivity_pos (P.length_pos e)) (P.sinc_pos hk e)

theorem SpectralNetwork.edgeWeight_zero (P : SpectralNetwork V E) (e : E) :
    P.edgeWeight 0 e = P.diffusivity / P.length e := by simp [edgeWeight]

theorem SpectralNetwork.edgeWeight_eq (P : SpectralNetwork V E) {k : ℝ}
    (hk : 0 < k) (e : E) :
    P.edgeWeight k e = P.diffusivity * k / Real.sin (k * P.length e) := by
  unfold edgeWeight
  rw [Real.sinc_of_ne_zero (ne_of_gt (mul_pos hk (P.length_pos e)))]
  field_simp [ne_of_gt hk, ne_of_gt (P.length_pos e)]

theorem SpectralNetwork.edgeWeight_continuousAt (P : SpectralNetwork V E) {k : ℝ}
    (hk : P.BelowFirstPole k) (e : E) : ContinuousAt (fun t => P.edgeWeight t e) k :=
  continuousAt_const.div
    (Real.continuous_sinc.continuousAt.comp
      (continuousAt_id.mul continuousAt_const)) (ne_of_gt (P.sinc_pos hk e))

theorem SpectralNetwork.nodalForm_zero (P : SpectralNetwork V E)
    [Fintype V] [Fintype E] (U : V → ℝ) :
    P.nodalForm 0 U =
      (∑ e, (P.diffusivity / P.length e) * (U (P.tail e) - U (P.head e)) ^ 2) +
        ∑ v, P.strength v * U v ^ 2 := by
  unfold nodalForm
  simp only [P.edgeWeight_zero, zero_mul, Real.cos_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem SpectralNetwork.nodalForm_zero_pos [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) {U : V → ℝ} (hU : U ≠ 0) : 0 < P.nodalForm 0 U := by
  rw [P.nodalForm_zero]
  have he : 0 ≤ ∑ e, (P.diffusivity / P.length e) * (U (P.tail e) - U (P.head e)) ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (div_pos P.diffusivity_pos (P.length_pos e)).le (sq_nonneg _)
  have hv : ∃ v, U v ≠ 0 := by
    by_contra! h
    exact hU (funext h)
  obtain ⟨v, hv⟩ := hv
  have ht : 0 < ∑ w, P.strength w * U w ^ 2 := by
    apply Finset.sum_pos'
    · intro w _
      exact mul_nonneg (P.strength_pos w).le (sq_nonneg _)
    · exact ⟨v, Finset.mem_univ v, mul_pos (P.strength_pos v) (sq_pos_of_ne_zero hv)⟩
  exact add_pos_of_nonneg_of_pos he ht

theorem SpectralNetwork.nodalForm_scale [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) (k c : ℝ) (U : V → ℝ) :
    P.nodalForm k (fun v => c * U v) = c ^ 2 * P.nodalForm k U := by
  unfold nodalForm
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem SpectralNetwork.nodalForm_abs_le [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) {k : ℝ} (hk : P.BelowFirstPole k) (U : V → ℝ) :
    P.nodalForm k (fun v => |U v|) ≤ P.nodalForm k U := by
  unfold nodalForm
  simp only [sq_abs]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (P.edgeWeight_pos hk e).le
  have hp : U (P.tail e) * U (P.head e) ≤ |U (P.tail e)| * |U (P.head e)| := by
    rw [← abs_mul]
    exact le_abs_self _
  nlinarith

theorem SpectralNetwork.nodalForm_operator [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) (k : ℝ) (U : V → ℝ) :
    P.nodalForm k U = ∑ v, U v * P.nodalOperator k U v := by
  have he : (∑ e, P.edgeWeight k e * (Real.cos (k * P.length e) *
      (U (P.tail e) ^ 2 + U (P.head e) ^ 2) - 2 * U (P.tail e) * U (P.head e))) =
      ∑ e, (P.rightEndpointFlux k U e * U (P.head e) - P.leftEndpointFlux k U e * U (P.tail e)) := by
    apply Finset.sum_congr rfl
    intro e _
    unfold leftEndpointFlux rightEndpointFlux
    ring
  unfold nodalForm nodalOperator
  rw [he, incidence_boundary_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ v, P.strength v * U v ^ 2) = ∑ v, U v * (P.strength v * U v) := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hs]
  ring

end TimeTraps.Spectral
