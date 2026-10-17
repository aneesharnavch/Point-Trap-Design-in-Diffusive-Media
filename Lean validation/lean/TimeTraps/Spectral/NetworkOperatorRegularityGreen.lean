module

public import TimeTraps.Spectral.NetworkOperatorRegularityEdges
public import TimeTraps.Analysis.IntervalPointRegularityGreen

@[expose] public section

/-! Green's identity for the full edge AC/L2 slope representatives and
arbitrary graph H1 tests. The signed vertex slope is the tail sum minus
the head sum, so a loop contributes at both of its endpoint traces. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def SpectralNetwork.operatorSlopeFlux (P : SpectralNetwork V E)
    (j : E → ℝ → ℝ) : V → ℝ :=
  vertexFlux P.tail P.head (fun e => j e 0) (fun e => j e (P.length e))

omit [Fintype V] in
theorem SpectralNetwork.operatorSlopeFlux_eq_sums (P : SpectralNetwork V E)
    (j : E → ℝ → ℝ) (v : V) :
    P.operatorSlopeFlux j v =
      (∑ e, if P.tail e = v then j e 0 else 0) -
        ∑ e, if P.head e = v then j e (P.length e) else 0 := by
  classical
  unfold operatorSlopeFlux vertexFlux incidenceLoad
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem SpectralNetwork.operator_slopes_green (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) {u j : E → ℝ → ℝ}
    (hj : ∀ e, IntervalSlopeRegularity (u e) (j e)
      (fun x => -(f e) x / P.diffusivity) 0 (P.length e))
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w) :
    (∑ e, ∫ x in (0 : ℝ)..P.length e,
      P.diffusivity * deriv (u e) x * deriv (w e) x) =
      (∑ e, ∫ x in (0 : ℝ)..P.length e, (f e) x * w e x) -
        ∑ v, P.diffusivity * P.operatorSlopeFlux j v * W v := by
  have hedge (e : E) : (∫ x in (0 : ℝ)..P.length e,
      P.diffusivity * deriv (u e) x * deriv (w e) x) =
      (∫ x in (0 : ℝ)..P.length e, (f e) x * w e x) +
        P.diffusivity * (j e (P.length e) * W (P.head e) - j e 0 * W (P.tail e)) := by
    have he := (hj e).poisson_green_identity P.diffusivity_pos.ne'
      (P.length_pos e).le (hw.edge_energy e)
    have ht : w e 0 = W (P.tail e) := hw.tail_value e
    have hh : w e (P.length e) = W (P.head e) := hw.head_value e
    rw [ht, hh] at he
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
    linarith
  have hb : (∑ e, (j e (P.length e) * W (P.head e) - j e 0 * W (P.tail e))) =
      -(∑ v, W v * P.operatorSlopeFlux j v) :=
    incidence_boundary_sum P.tail P.head (fun e => j e 0) (fun e => j e (P.length e)) W
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb, mul_neg, Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  ring

end TimeTraps.Spectral
