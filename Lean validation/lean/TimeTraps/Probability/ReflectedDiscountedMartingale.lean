module

public import TimeTraps.Probability.ReflectedDiscountedContinuation
public import TimeTraps.Probability.ReflectedDiscountedDecomposition
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The discounted resolvent martingale for the original raw Brownian
filtration. Its canonical raw representative is the conditional expectation
of the actual total discounted payoff. At each fixed time it equals the
literal discounted resolvent plus the accumulated ordinary time integral. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedDiscountedResolvent (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (D α x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-α * t.val) * reflectedContinuousInput L hL D x
    (reflectedFellerLaplace L hL D α f) (B t ω) + reflectedDiscountedPast B L hL D α x f t ω

def reflectedDiscountedResolventVersion (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t))
    (P : Measure Ω) (L : ℝ) (hL : 0 < L) (D α x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) : Ω → ℝ :=
  P[reflectedDiscountedFuture B L hL D α x f 0 | brownianNaturalFiltration B hBm t]

theorem reflectedDiscountedResolventVersion_martingale (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D α x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Martingale (reflectedDiscountedResolventVersion B hBm P L hL D α x f)
      (brownianNaturalFiltration B hBm) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact martingale_condExp _ _ _

theorem reflectedDiscountedResolventVersion_ae (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) :
    reflectedDiscountedResolventVersion B hBm P L hL D α x f t =ᵐ[P]
      reflectedDiscountedResolvent B L hL D α x f t := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let A := reflectedDiscountedPast B L hL D α x f t
  let V := reflectedDiscountedFuture B L hL D α x f t
  let c := Real.exp (-α * t.val)
  let m := brownianNaturalFiltration B hBm t
  have hAi : Integrable A P := reflectedDiscountedPast_integrable hjoint L hL D x hα f t
  have hVi : Integrable V P := reflectedDiscountedFuture_integrable B hjoint L hL D x hα f t
  have hdec : reflectedDiscountedFuture B L hL D α x f 0 =ᵐ[P] A + c • V :=
    reflectedDiscounted_decomposition hjoint L hL D x hα f t
  have hsum := condExp_add hAi (hVi.smul c) m
  have hsmul := condExp_smul (μ := P) c V m
  have hA : P[A | m] =ᵐ[P] A := condExp_of_aestronglyMeasurable'
    ((brownianNaturalFiltration B hBm).le t)
    (reflectedDiscountedPast_aestronglyMeasurable hB hBm L hL D x hα f t) hAi
  have hV := reflectedDiscountedFuture_condExp hB.toIsPreBrownianReal hBm hjoint L hL D hD x hα f t
  filter_upwards [condExp_congr_ae (m := m) hdec, hsum, hsmul, hA, hV] with ω hd hs hm ha hv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs hm
  change P[reflectedDiscountedFuture B L hL D α x f 0 | m] ω =
    c * reflectedContinuousInput L hL D x (reflectedFellerLaplace L hL D α f) (B t ω) + A ω
  rw [hd, hs, hm, ha, hv]
  ring

theorem reflectedDiscountedResolventVersion_physical_ae (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) :
    reflectedDiscountedResolventVersion B hBm P L hL D α x f t =ᵐ[P]
      (fun ω => Real.exp (-α * t.val) * reflectedFellerLaplace L hL D α f
        ⟨foldedTrajectory L D x B t ω, foldedTrajectory_mem L hL D x B t ω⟩ +
        ∫ r in (0 : ℝ)..t.val, Real.exp (-α * r) *
          f ⟨foldedTrajectory L D x B r.toNNReal ω, foldedTrajectory_mem L hL D x B r.toNNReal ω⟩) :=
  reflectedDiscountedResolventVersion_ae hB hBm hjoint L hL D hD x hα f t

theorem reflectedDiscountedResolvent_condExp (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[reflectedDiscountedResolvent B L hL D α x f t | brownianNaturalFiltration B hBm s] =ᵐ[P]
      reflectedDiscountedResolvent B L hL D α x f s := by
  exact (condExp_congr_ae (reflectedDiscountedResolventVersion_ae hB hBm hjoint L hL D hD x hα f t).symm).trans
    (((reflectedDiscountedResolventVersion_martingale hB.toIsPreBrownianReal hBm L hL D α x f).2 s t hst).trans
      (reflectedDiscountedResolventVersion_ae hB hBm hjoint L hL D hD x hα f s))

end TimeTraps.Probability

end
