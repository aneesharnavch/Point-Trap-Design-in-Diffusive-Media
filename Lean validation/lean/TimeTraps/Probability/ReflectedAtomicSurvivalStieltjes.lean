module

public import TimeTraps.Probability.ReflectedAtomicHazardStieltjes
public import TimeTraps.Probability.StieltjesExponentialSubstitution

@[expose] public section

/-! The actual increasing loss of survival, 1-exp(-A), and its Stieltjes
integrals. On the finite-label regular event, its measure integrates a
continuous time weight as that weight times the literal survival against
the actual hazard measure. The hazard remains normalized as sum κ ell. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

def reflectedAtomicSurvivalLossStieltjes (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  stieltjesExponential (reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω)
    (reflectedAtomicHazardStieltjes_continuous L hL D hD x a κ hκ ω)

theorem reflectedAtomicSurvivalLossStieltjes_continuous
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) :
    Continuous (reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω) :=
  stieltjesExponential_continuous _ _

theorem reflectedAtomicSurvivalLossStieltjes_apply
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω) (r : ℝ) :
    reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω r =
      1 - reflectedAtomicSurvival L D x a κ r.toNNReal ω := by
  change 1 - Real.exp (-reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω r) = _
  rw [reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω r]
  rfl

theorem reflectedAtomicSurvivalLossStieltjes_apply_nnreal
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω) (t : ℝ≥0) :
    reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω t.val =
      1 - reflectedAtomicSurvival L D x a κ t ω := by
  exact (reflectedAtomicSurvivalLossStieltjes_apply L hL D hD x a κ hκ hω t.val).trans
    (congrArg (fun q => 1 - reflectedAtomicSurvival L D x a κ q ω) (Real.toNNReal_coe (r := t)))

theorem reflectedAtomicSurvivalLossStieltjes_zero
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω) :
    reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω 0 = 0 := by
  change 1 - Real.exp (-reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω 0) = 0
  rw [reflectedAtomicHazardStieltjes_zero L hL D hD x a κ hκ hω,
    neg_zero, Real.exp_zero, sub_self]

theorem reflectedAtomicSurvivalLoss_weighted_integrable
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    IntegrableOn (fun r => g r.toNNReal) (Ioc (0 : ℝ) T.val)
      (reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω).measure ∧
    IntegrableOn (fun r => g r.toNNReal * reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      (Ioc (0 : ℝ) T.val) (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) := by
  have he := stieltjesExponential_weighted_integrable
    (reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω)
    (reflectedAtomicHazardStieltjes_continuous L hL D hD x a κ hκ ω) g hg T
  refine ⟨he.1, ?_⟩
  simpa only [reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω,
    reflectedAtomicSurvival, reflectedAtomicHazardTimeMeasure] using he.2

theorem reflectedAtomicSurvivalLoss_weighted_integral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal
      ∂(reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω).measure) =
      ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal * reflectedAtomicSurvival L D x a κ r.toNNReal ω
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω := by
  have he := stieltjesExponential_weighted_integral
    (reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω)
    (reflectedAtomicHazardStieltjes_continuous L hL D hD x a κ hκ ω) g hg T
  simpa only [reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω,
    reflectedAtomicSurvival, reflectedAtomicHazardTimeMeasure,
    reflectedAtomicSurvivalLossStieltjes] using he

end TimeTraps.Probability

end
