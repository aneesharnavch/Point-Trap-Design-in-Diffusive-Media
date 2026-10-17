module

public import TimeTraps.Probability.ReflectedCosineDynkinConditional
public import TimeTraps.Probability.ReflectedCosineDynkinProcess
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The Neumann-cosine Dynkin identity conditioned on the original
Brownian past, and actual raw-filtration martingale representatives.
The representatives equal the physical expression at each fixed time;
no completion of the filtration is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedCosineDynkin_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (n : ℕ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[reflectedCosineDynkin B L D x n t | brownianNaturalFiltration B hBm s] =ᵐ[P]
      reflectedCosineDynkin B L D x n s := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let C (r : ℝ≥0) : Ω → ℝ := fun ω => reflectedCosineInput L D x n (B r ω)
  let A (r : ℝ≥0) := brownianItoDrift B (reflectedCosineInput L D x n) r
  let a : ℝ := D * ((n : ℝ) * Real.pi / L) ^ 2
  let m := brownianNaturalFiltration B hBm s
  let I : ℝ := ∫ r in s.val..t.val, Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (r - s.val))
  have hg := reflectedCosineInput_lipschitz L D x n
  have hCi (r : ℝ≥0) : Integrable (C r) P :=
    (brownianLipschitz_eval_memLp hB hg r).integrable (by norm_num)
  have hAi (r : ℝ≥0) : Integrable (A r) P :=
    (brownianItoDrift_memLp hB hg hjoint r).integrable (by norm_num)
  have h0m : StronglyMeasurable[m] (C 0) := hg.continuous.comp_stronglyMeasurable
    ((brownianNaturalFiltration_stronglyAdapted B hBm 0).mono
      ((brownianNaturalFiltration B hBm).mono (show (0 : ℝ≥0) ≤ s from zero_le)))
  have h0 : P[C 0 | m] =ᵐ[P] C 0 := condExp_of_aestronglyMeasurable'
    ((brownianNaturalFiltration B hBm).le s) h0m.aestronglyMeasurable (hCi 0)
  have hl : P[C t - C 0 + a • A t | m] =ᵐ[P]
      P[C t | m] - P[C 0 | m] + a • P[A t | m] :=
    (condExp_add ((hCi t).sub (hCi 0)) ((hAi t).smul a) m).trans
      ((condExp_sub (hCi t) (hCi 0) m).add (condExp_smul a (A t) m))
  have hs := condExp_sub (hAi t) (hAi s) m
  have hd := reflectedCosine_drift_increment_condExp hB hBm hjoint L hL D hD x n hst
  have hp := brownianItoDrift_condExp_past hB hBm hg hjoint (le_refl s)
  have ht := reflectedCosineInput_condExp hB hBm L hL D hD x n hst
  have hexp : Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (t.val - s.val)) + a * I = 1 := by
    simpa only [a, I, neg_mul] using exponential_decay_integral_identity a s.val t.val
  filter_upwards [hl, hs, hd, hp, ht, h0] with ω hlω hsω hdω hpω htω h0ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hlω hsω
  have hA : P[A t | m] ω = A s ω + I * C s ω := by
    change P[A t - A s | m] ω = I * C s ω at hdω
    change P[A s | m] ω = A s ω at hpω
    rw [hsω, hpω] at hdω
    linarith
  change P[C t - C 0 + a • A t | m] ω = C s ω - C 0 ω + a * A s ω
  rw [hlω, htω, h0ω, hA]
  calc
    _ = (Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (t.val - s.val)) + a * I) *
        C s ω - C 0 ω + a * A s ω := by ring
    _ = _ := by rw [hexp, one_mul]

noncomputable def reflectedCosineDynkinVersion (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω)
    (L D x : ℝ) (n : ℕ) (t : ℝ≥0) : Ω → ℝ :=
  P[reflectedCosineDynkin B L D x n t | brownianNaturalFiltration B hBm t]

theorem reflectedCosineDynkinVersion_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L D x : ℝ) (n : ℕ) (t : ℝ≥0) :
    reflectedCosineDynkinVersion B hBm P L D x n t =ᵐ[P] reflectedCosineDynkin B L D x n t := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact condExp_of_aestronglyMeasurable' ((brownianNaturalFiltration B hBm).le t)
    (reflectedCosineDynkin_aestronglyMeasurable hB hBm hjoint L D x n t)
    ((reflectedCosineDynkin_memLp hB hjoint L D x n t).integrable (by norm_num))

theorem reflectedCosineDynkinVersion_martingale (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (n : ℕ) :
    Martingale (reflectedCosineDynkinVersion B hBm P L D x n) (brownianNaturalFiltration B hBm) P := by
  refine ⟨fun _ => stronglyMeasurable_condExp, fun s t hst => ?_⟩
  exact (condExp_congr_ae (reflectedCosineDynkinVersion_ae hB hBm hjoint L D x n t)).trans
    ((reflectedCosineDynkin_condExp hB hBm hjoint L hL D hD x n hst).trans
      (reflectedCosineDynkinVersion_ae hB hBm hjoint L D x n s).symm)

theorem reflectedCosineDynkinVersion_physical_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (n : ℕ) (t : ℝ≥0) :
    reflectedCosineDynkinVersion B hBm P L D x n t =ᵐ[P] (fun ω =>
      Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B t ω) -
        Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B 0 ω) -
      D * (∫ r in (0 : ℝ)..t.val,
        deriv (deriv (fun z : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * z)))
          (foldedTrajectory L D x B r.toNNReal ω))) :=
  (reflectedCosineDynkinVersion_ae hB hBm hjoint L D x n t).trans
    (Eventually.of_forall (reflectedCosineDynkin_physical B L hL D x n t))

theorem brownianDyadic_reflectedCosine_dynkin_martingale
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (n : ℕ) :
    Martingale (reflectedCosineDynkinVersion brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure L D x n) brownianFiltration brownianDyadicMeasure :=
  reflectedCosineDynkinVersion_martingale brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x n

end TimeTraps.Probability
