module

public import TimeTraps.Analysis.GraphSingleTraceControl
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! The original positive continuous conductance has a positive lower
bound on the finite graph. Its weighted derivative form therefore controls
the unweighted derivative energy used by the actual graph H1 norm. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype E]

noncomputable def graphConductanceSquare (G : MetricGraph V E) (u : E → ℝ → ℝ) : ℝ :=
  ∑ e, ∫ x in (0 : ℝ)..G.length e, G.conductance e x * deriv (u e) x ^ 2

theorem graphConductanceSquare_nonneg (G : MetricGraph V E) (u : E → ℝ → ℝ) :
    0 ≤ graphConductanceSquare G u :=
  Finset.sum_nonneg (fun e _ => intervalIntegral.integral_nonneg (G.length_pos e).le
    (fun x hx => mul_nonneg (G.conductance_pos e x hx).le (sq_nonneg _)))

theorem graphConductance_lower_bound [Nonempty E] (G : MetricGraph V E) :
    ∃ m : ℝ, 0 < m ∧ ∀ e x, x ∈ Icc 0 (G.length e) → m ≤ G.conductance e x := by
  classical
  have hedge (e : E) : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc 0 (G.length e), m ≤ G.conductance e x := by
    obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) (G.length e)).Nonempty from ⟨0, le_rfl, (G.length_pos e).le⟩)
      (G.conductance_continuous e)
    exact ⟨G.conductance e x, G.conductance_pos e x hx, hmin⟩
  choose m hm hb using hedge
  obtain ⟨e, _, he⟩ := Finset.exists_min_image Finset.univ m Finset.univ_nonempty
  exact ⟨m e, hm e, fun d x hx => (he d (Finset.mem_univ d)).trans (hb d x hx)⟩

theorem graphDerivativeSquare_le_conductance {G : MetricGraph V E} {m : ℝ}
    (hm : 0 < m) (hbound : ∀ e x, x ∈ Icc 0 (G.length e) → m ≤ G.conductance e x)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) :
    graphDerivativeSquare G u ≤ m⁻¹ * graphConductanceSquare G u := by
  have he (e : E) : m * (∫ x in (0 : ℝ)..G.length e, deriv (u e) x ^ 2) ≤
      ∫ x in (0 : ℝ)..G.length e, G.conductance e x * deriv (u e) x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (G.length_pos e).le
      ((hu.edge_energy e).derivative_square_integrable.const_mul m)
      ((hu.edge_energy e).weighted_square_integrable (by
        simpa only [uIcc_of_le (G.length_pos e).le] using G.conductance_continuous e))
    intro x hx
    exact mul_le_mul_of_nonneg_right (hbound e x hx) (sq_nonneg _)
  have h : m * graphDerivativeSquare G u ≤ graphConductanceSquare G u := by
    unfold graphDerivativeSquare graphConductanceSquare
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => he e)
  have hh := mul_le_mul_of_nonneg_left h (inv_pos.mpr hm).le
  rwa [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul] at hh

end TimeTraps.Analysis
