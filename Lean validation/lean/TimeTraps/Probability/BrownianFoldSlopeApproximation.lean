module

public import TimeTraps.Probability.BrownianFiniteSignIntegrand
public import TimeTraps.Analysis.ReflectedFoldTanakaSlope

@[expose] public section

/-! The paired affine-fold slope sums are actual normalized Brownian
integrands. The diffusion scale is outside their stochastic integrals:
these integrands represent H_N(x + sigma B), whose absolute value is at
most one. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianAffineSign_identity (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (a z : ℝ) :
    Real.sign (x + σ * z - a) = Real.sign (z - (a - x) / σ) := by
  have he : x + σ * z - a = σ * (z - (a - x) / σ) := by
    field_simp
    ring
  rw [he]
  rcases lt_trichotomy (z - (a - x) / σ) 0 with hn | hz | hp
  · rw [Real.sign_of_neg hn, Real.sign_of_neg (mul_neg_of_pos_of_neg hσ hn)]
  · rw [hz, mul_zero]
  · rw [Real.sign_of_pos hp, Real.sign_of_pos (mul_pos hσ hp)]

theorem brownianFoldSlopeApprox_affine (L x : ℝ) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (z : ℝ) :
    reflectedFoldTanakaSlopeApprox L N (x + σ * z) =
      Real.sign (z - (0 - x) / σ) +
      ((∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) *
        Real.sign (z - ((j + 1 : ℕ) * L - x) / σ)) +
       ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) *
        Real.sign (z - (-(j + 1 : ℕ) * L - x) / σ)) := by
  rw [reflectedFoldTanakaSlopeApprox, ← Finset.sum_add_distrib]
  rw [show Real.sign (x + σ * z) = Real.sign (z - (0 - x) / σ) by
    simpa only [sub_zero] using brownianAffineSign_identity x hσ 0 z]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [brownianAffineSign_identity x hσ ((j + 1 : ℕ) * L) z,
    show Real.sign (x + σ * z + (j + 1 : ℕ) * L) =
      Real.sign (z - (-(j + 1 : ℕ) * L - x) / σ) by
        simpa only [sub_neg_eq_add, neg_mul] using
          brownianAffineSign_identity x hσ (-((j + 1 : ℕ) * L)) z]
  ring

theorem brownianFoldSlopeApprox_measurable (L x σ : ℝ) (N : ℕ) :
    Measurable (fun z : ℝ => reflectedFoldTanakaSlopeApprox L N (x + σ * z)) := by
  have hm : Measurable (fun z : ℝ => x + σ * z) :=
    (measurable_id.const_mul σ).const_add x
  unfold reflectedFoldTanakaSlopeApprox
  apply (brownianSign_measurable.comp hm).add
  apply Finset.measurable_fun_sum
  intro j _
  exact ((brownianSign_measurable.comp (hm.sub_const ((j + 1 : ℕ) * L))).add
    (brownianSign_measurable.comp (hm.add_const ((j + 1 : ℕ) * L)))).const_mul ((-1 : ℝ) ^ (j + 1))

noncomputable def brownianFoldSlopeApproxIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L x σ : ℝ) (N : ℕ) (T : ℝ≥0) : brownianIntegralSpace B hBm P :=
  brownianSignIntegrand hB hBm hjoint ((0 - x) / σ) T +
    (brownianFiniteSignIntegrand hB hBm hjoint (Finset.range N) (fun j => (-1 : ℝ) ^ (j + 1))
      (fun j => ((j + 1 : ℕ) * L - x) / σ) T +
     brownianFiniteSignIntegrand hB hBm hjoint (Finset.range N) (fun j => (-1 : ℝ) ^ (j + 1))
      (fun j => (-(j + 1 : ℕ) * L - x) / σ) T)

theorem brownianFoldSlopeApproxIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L x : ℝ) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (T : ℝ≥0) :
    (brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianBoundedProcess B (fun z => reflectedFoldTanakaSlopeApprox L N (x + σ * z)) T := by
  let C := brownianSignIntegrand hB hBm hjoint ((0 - x) / σ) T
  let U := brownianFiniteSignIntegrand hB hBm hjoint (Finset.range N)
    (fun j => (-1 : ℝ) ^ (j + 1)) (fun j => ((j + 1 : ℕ) * L - x) / σ) T
  let V := brownianFiniteSignIntegrand hB hBm hjoint (Finset.range N)
    (fun j => (-1 : ℝ) ^ (j + 1)) (fun j => (-(j + 1 : ℕ) * L - x) / σ) T
  change ((C : Lp ℝ 2 ((volume : Measure ℝ).prod P)) +
    ((U : Lp ℝ 2 ((volume : Measure ℝ).prod P)) + (V : Lp ℝ 2 ((volume : Measure ℝ).prod P))))
    =ᵐ[volume.prod P] _
  filter_upwards [Lp.coeFn_add (C : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      ((U : Lp ℝ 2 ((volume : Measure ℝ).prod P)) + (V : Lp ℝ 2 ((volume : Measure ℝ).prod P))),
    Lp.coeFn_add (U : Lp ℝ 2 ((volume : Measure ℝ).prod P)) (V : Lp ℝ 2 ((volume : Measure ℝ).prod P)),
    brownianSignIntegrand_coe hB hBm hjoint ((0 - x) / σ) T,
    brownianFiniteSignIntegrand_coe hB hBm hjoint (Finset.range N)
      (fun j => (-1 : ℝ) ^ (j + 1)) (fun j => ((j + 1 : ℕ) * L - x) / σ) T,
    brownianFiniteSignIntegrand_coe hB hBm hjoint (Finset.range N)
      (fun j => (-1 : ℝ) ^ (j + 1)) (fun j => (-(j + 1 : ℕ) * L - x) / σ) T]
    with p hadd hsum hc hu hv
  rw [hadd, Pi.add_apply, hsum, Pi.add_apply, hc, hu, hv]
  change _ = (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
    reflectedFoldTanakaSlopeApprox L N (x + σ * B p.1.toNNReal p.2)
  rw [brownianFoldSlopeApprox_affine L x hσ N]
  unfold brownianBoundedProcess brownianSquareProcess
  ring

theorem brownianFoldSlopeApproxIntegrand_integral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L x σ : ℝ) (N : ℕ) (T : ℝ≥0) :
    brownianIntegral hB (brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T) =
      brownianSignIntegral hB hBm hjoint ((0 - x) / σ) T +
        ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) •
          (brownianSignIntegral hB hBm hjoint (((j + 1 : ℕ) * L - x) / σ) T +
           brownianSignIntegral hB hBm hjoint ((-(j + 1 : ℕ) * L - x) / σ) T) := by
  simp only [brownianFoldSlopeApproxIntegrand, map_add, brownianFiniteSignIntegrand_integral,
    brownianSignIntegral, smul_add, Finset.sum_add_distrib]

end TimeTraps.Probability
