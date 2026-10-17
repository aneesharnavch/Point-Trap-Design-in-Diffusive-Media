module

public import TimeTraps.Analysis.GraphSobolevSpacePhysical
public import TimeTraps.Analysis.IntervalEnergyTrace

@[expose] public section

/-! Connectivity propagates control of differences of vertex traces using
only the actual edge derivative integrals. Constants depend on the graph,
not on the state, and no reaction coefficient is used in this step. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype E]

noncomputable def graphDerivativeSquare (G : MetricGraph V E) (u : E → ℝ → ℝ) : ℝ :=
  ∑ e, ∫ x in (0 : ℝ)..G.length e, deriv (u e) x ^ 2

theorem graphDerivativeSquare_nonneg (G : MetricGraph V E) (u : E → ℝ → ℝ) :
    0 ≤ graphDerivativeSquare G u :=
  Finset.sum_nonneg (fun e _ => intervalIntegral.integral_nonneg_of_forall
    (G.length_pos e).le (fun x => sq_nonneg (deriv (u e) x)))

theorem graphDerivativeSquare_edge_le (G : MetricGraph V E) (u : E → ℝ → ℝ) (e : E) :
    (∫ x in (0 : ℝ)..G.length e, deriv (u e) x ^ 2) ≤ graphDerivativeSquare G u := by
  classical
  unfold graphDerivativeSquare
  exact Finset.single_le_sum (fun d _ => intervalIntegral.integral_nonneg_of_forall
    (G.length_pos d).le (fun x => sq_nonneg (deriv (u d) x))) (Finset.mem_univ e)

theorem graphEnergy_endpoint_sub_sq_le {G : MetricGraph V E} {U : V → ℝ}
    {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (e : E) :
    (U (G.tail e) - U (G.head e)) ^ 2 ≤ G.length e * graphDerivativeSquare G u := by
  have h := (hu.edge_energy e).sub_sq_le
    (show (0 : ℝ) ∈ Icc 0 (G.length e) from ⟨le_rfl, (G.length_pos e).le⟩)
    (show G.length e ∈ Icc 0 (G.length e) from ⟨(G.length_pos e).le, le_rfl⟩)
  simp only [hu.tail_value, hu.head_value, zero_sub, abs_neg, abs_of_pos (G.length_pos e)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (graphDerivativeSquare_edge_le G u e)
    (G.length_pos e).le)

theorem graphSingleTrace_difference_control (G : MetricGraph V E) (v w : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy G U u →
      (U v - U w) ^ 2 ≤ C * graphDerivativeSquare G u := by
  induction G.connected v w with
  | rel v w hvw =>
      obtain ⟨e, rfl, rfl⟩ := hvw
      exact ⟨G.length e, (G.length_pos e).le, fun _ _ hu => graphEnergy_endpoint_sub_sq_le hu e⟩
  | refl v =>
      exact ⟨0, le_rfl, fun _ _ _ => by simp⟩
  | symm v w _ ih =>
      obtain ⟨C, hC, hb⟩ := ih
      refine ⟨C, hC, ?_⟩
      intro U u hu
      simpa only [sub_sq_comm] using hb U u hu
  | trans v w z _ _ ih₁ ih₂ =>
      obtain ⟨C, hC, hb⟩ := ih₁
      obtain ⟨D, hD, hd⟩ := ih₂
      refine ⟨2 * (C + D), mul_nonneg (by norm_num) (add_nonneg hC hD), ?_⟩
      intro U u hu
      have h₁ := hb U u hu
      have h₂ := hd U u hu
      nlinarith [sq_nonneg ((U v - U w) - (U w - U z))]

theorem graphSingleTrace_uniform_difference_control [Fintype V]
    (G : MetricGraph V E) (v₀ : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy G U u →
      ∀ v, (U v - U v₀) ^ 2 ≤ C * graphDerivativeSquare G u := by
  classical
  choose C hC hb using fun v => graphSingleTrace_difference_control G v v₀
  refine ⟨∑ v, C v, Finset.sum_nonneg (fun v _ => hC v), ?_⟩
  intro U u hu v
  exact (hb v U u hu).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun w _ => hC w) (Finset.mem_univ v))
    (graphDerivativeSquare_nonneg G u))

end TimeTraps.Analysis
