module

public import TimeTraps.Spectral.CompactInverseResolventDomain
public import TimeTraps.Spectral.CompactInverseResolventEulerScalar
public import TimeTraps.Analysis.CompactSpectralSemigroupContinuity

@[expose] public section

/-! Strong Euler convergence of powers of the actual inverse resolvent to
the already constructed heat semigroup. Parseval and a summable bound
justify passage from scalar limits to the full Hilbert norm, with no
finite-dimensional or countable-basis premise. Time zero is included. -/

namespace TimeTraps.Analysis

open Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.resolvent_pow_inner {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (n : ℕ) (x : E) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (((h.resolvent s) ^ n) x) =
      compactResolventCoefficient s i ^ n * inner ℝ (h.eigenbasis i) x := by
  induction n generalizing x with
  | zero => simp only [pow_zero, one_apply_eq_self, one_mul]
  | succ n ih =>
      simp only [pow_succ, mul_apply_eq_comp, ih, h.resolvent_inner]
      ring

theorem CompactPositiveInverse.resolvent_euler_difference_sq {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (n : ℕ) (x : E) :
    ‖((h.resolvent (t / (n : ℝ≥0))) ^ n) x - h.heatSemigroup t x‖ ^ 2 =
      ∑' i : CompactSpectralIndex T,
        ((compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n - compactHeatCoefficient t i) *
          inner ℝ (h.eigenbasis i) x) ^ 2 := by
  rw [← h.parseval (((h.resolvent (t / (n : ℝ≥0))) ^ n) x - h.heatSemigroup t x)]
  apply tsum_congr
  intro i
  rw [inner_sub_right, h.resolvent_pow_inner, h.heatSemigroup_inner, sub_mul]

theorem CompactPositiveInverse.resolvent_euler_tendsto {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : E) :
    Tendsto (fun n : ℕ => ((h.resolvent (t / (n : ℝ≥0))) ^ n) x)
      atTop (𝓝 (h.heatSemigroup t x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hp : ∀ i : CompactSpectralIndex T,
      Tendsto (fun n : ℕ =>
        ((compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n - compactHeatCoefficient t i) *
          inner ℝ (h.eigenbasis i) x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    intro i
    simpa only [sub_self, zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
      (((h.resolvent_euler_coefficient_tendsto t i).sub_const
        (compactHeatCoefficient t i)).mul_const (inner ℝ (h.eigenbasis i) x)).pow 2
  have hb : ∀ n : ℕ, ∀ i : CompactSpectralIndex T,
      ‖((compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n - compactHeatCoefficient t i) *
        inner ℝ (h.eigenbasis i) x) ^ 2‖ ≤ (inner ℝ (h.eigenbasis i) x) ^ 2 := by
    intro n i
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have hd := h.resolvent_euler_coefficient_bound t n i
    have hd₂ : (compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n -
        compactHeatCoefficient t i) ^ 2 ≤ 1 := by
      have hp₀ := mul_nonneg (sub_nonneg.mpr hd)
        (show 0 ≤ 1 + |compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n -
          compactHeatCoefficient t i| by positivity)
      nlinarith [sq_abs (compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n -
        compactHeatCoefficient t i)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hd₂ (sq_nonneg (inner ℝ (h.eigenbasis i) x))
  have hd := tendsto_tsum_of_dominated_convergence (h.hasSum_parseval x).summable hp
    (Eventually.of_forall hb)
  have hn : Tendsto (fun n : ℕ =>
      ‖((h.resolvent (t / (n : ℝ≥0))) ^ n) x - h.heatSemigroup t x‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [← h.resolvent_euler_difference_sq, tsum_zero] using hd
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

end TimeTraps.Analysis
