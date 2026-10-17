module

public import TimeTraps.Spectral.NetworkKernel
public import TimeTraps.Spectral.FirstZero
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

/-! Compact first-zero construction for the finite endpoint form. The terminal
negative test remains an explicit premise until the next analytic bound. -/

namespace TimeTraps.Spectral

open Set Filter
open scoped BigOperators Topology

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem SpectralNetwork.belowFirstPole_of_le (P : SpectralNetwork V E) {k B : ℝ}
    (hB : P.BelowFirstPole B) (hk : 0 ≤ k) (hle : k ≤ B) : P.BelowFirstPole k :=
  ⟨hk, fun e => (mul_le_mul_of_nonneg_right hle (P.length_pos e).le).trans_lt (hB.2 e)⟩

theorem SpectralNetwork.nodalForm_continuous_family (P : SpectralNetwork V E)
    (c : ℝ → ℝ) (hc : Continuous c) (hp : ∀ t, P.BelowFirstPole (c t)) :
    Continuous (fun p : ℝ × (V → ℝ) => P.nodalForm (c p.1) p.2) := by
  have hw (e : E) : Continuous (fun t => P.edgeWeight (c t) e) :=
    continuous_iff_continuousAt.mpr fun t => (P.edgeWeight_continuousAt (hp t) e).comp hc.continuousAt
  have hv (v : V) : Continuous (fun p : ℝ × (V → ℝ) => p.2 v) :=
    (continuous_apply v).comp continuous_snd
  unfold nodalForm
  apply Continuous.add
  · apply continuous_finsetSum
    intro e _
    exact ((hw e).comp continuous_fst).mul
      (((Real.continuous_cos.comp ((hc.comp continuous_fst).mul continuous_const)).mul
        (((hv (P.tail e)).pow 2).add ((hv (P.head e)).pow 2))).sub
          ((continuous_const.mul (hv (P.tail e))).mul (hv (P.head e))))
  · apply continuous_finsetSum
    intro v _
    exact continuous_const.mul ((hv v).pow 2)

theorem SpectralNetwork.nodalForm_nonneg_of_sphere (P : SpectralNetwork V E) (k : ℝ)
    (h : ∀ U ∈ Metric.sphere (0 : V → ℝ) 1, 0 ≤ P.nodalForm k U) :
    ∀ U, 0 ≤ P.nodalForm k U := by
  intro U
  by_cases hU : U = 0
  · simp [hU, nodalForm]
  have hn : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hu : ‖U‖⁻¹ • U ∈ Metric.sphere (0 : V → ℝ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]
  have hz := h (‖U‖⁻¹ • U) hu
  change 0 ≤ P.nodalForm k (fun v => ‖U‖⁻¹ * U v) at hz
  rw [P.nodalForm_scale] at hz
  exact nonneg_of_mul_nonneg_right hz (sq_pos_of_pos (inv_pos.mpr hn))

theorem SpectralNetwork.positive_nodal_state_of_terminal_test [Nonempty V]
    (P : SpectralNetwork V E) {B : ℝ} (hB : 0 < B) (hpB : P.BelowFirstPole B)
    (hnegative : P.nodalForm B (fun _ => 1) ≤ 0) :
    ∃ k ∈ Ioc (0 : ℝ) B, P.BelowFirstPole k ∧
      (∀ W, 0 ≤ P.nodalForm k W) ∧
      ∃ U : V → ℝ, (∀ v, 0 < U v) ∧ ∀ v, P.nodalOperator k U v = 0 := by
  let c : ℝ → ℝ := fun t => max 0 (min t B)
  have hc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcp (t : ℝ) : P.BelowFirstPole (c t) :=
    P.belowFirstPole_of_le hpB (le_max_left _ _) (max_le hB.le (min_le_right _ _))
  have hc0 : c 0 = 0 := by simp [c, hB.le]
  have hcB : c B = B := by simp [c, hB.le]
  have hc_eq {t : ℝ} (ht : t ∈ Icc 0 B) : c t = t := by
    simp only [c, min_eq_left ht.2, max_eq_right ht.1]
  have hone : (fun _ : V => (1 : ℝ)) ∈ Metric.sphere (0 : V → ℝ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, pi_norm_const, norm_one]
  have hzero : ∀ U ∈ Metric.sphere (0 : V → ℝ) 1, 0 < P.nodalForm (c 0) U := by
    intro U hU
    rw [hc0]
    apply P.nodalForm_zero_pos
    intro hz
    norm_num [hz, Metric.mem_sphere] at hU
  obtain ⟨k, hk, _, hnonneg, U, hU, hUz⟩ := compact_first_zero
    (u := fun t W => P.nodalForm (c t) W)
    (isCompact_sphere (0 : V → ℝ) 1) ⟨(fun _ => 1), hone⟩
    (P.nodalForm_continuous_family c hc hcp) hB hzero
    ⟨(fun _ => 1), hone, by simpa only [hcB] using hnegative⟩
  have hck := hc_eq ⟨hk.1.le, hk.2⟩
  rw [hck] at hnonneg hUz
  have hps := P.belowFirstPole_of_le hpB hk.1.le hk.2
  have hglobal := P.nodalForm_nonneg_of_sphere k hnonneg
  let W : V → ℝ := fun v => |U v|
  have hwz : P.nodalForm k W = 0 :=
    le_antisymm ((P.nodalForm_abs_le hps U).trans_eq hUz) (hglobal W)
  have hwne : W ≠ 0 := by
    intro hz
    have huz : U = 0 := by
      funext v
      exact abs_eq_zero.mp (congrFun hz v)
    norm_num [huz, Metric.mem_sphere] at hU
  have hop := P.nodalOperator_zero_of_nodalForm_zero k hglobal hwz
  refine ⟨k, hk, hps, hglobal, W, ?_, hop⟩
  exact P.nonnegative_nodal_kernel_positive hps (fun v => abs_nonneg (U v)) hwne hop

end TimeTraps.Spectral
