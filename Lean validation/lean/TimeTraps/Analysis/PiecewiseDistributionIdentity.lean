module

public import TimeTraps.Analysis.PiecewiseDistributionPairing

@[expose] public section

/-! Equality of actual Mathlib distributions: the second derivative of the
continuous state distribution is its classical density on each piece plus
signed Dirac masses equal to right slope minus left slope at the cuts. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped Distributions

def piecewiseOpenInterval {n : ℕ} (q : Fin (n + 2) → ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (q 0) (q (Fin.last (n + 1))), isOpen_Ioo⟩

noncomputable def PiecewiseDerivativeData.stateDistribution {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g) :
    𝓓'(piecewiseOpenInterval q, ℝ) :=
  piecewiseIntervalDistribution (piecewiseOpenInterval q) (q 0) (q (Fin.last (n + 1)))
    (h.node_strictMono.monotone (Fin.zero_le _)) u
    (h.state_continuous.intervalIntegrable_of_Icc (h.node_strictMono.monotone (Fin.zero_le _)))

noncomputable def PiecewiseDerivativeData.densityDistribution {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g) :
    𝓓'(piecewiseOpenInterval q, ℝ) :=
  ∑ e : Fin (n + 1), piecewiseIntervalDistribution (piecewiseOpenInterval q)
    (q e.castSucc) (q e.succ) (h.node_strictMono Fin.castSucc_lt_succ).le (g e)
    (h.density_integrable e)

noncomputable def piecewiseJumpDistribution {n : ℕ} (q : Fin (n + 2) → ℝ)
    (j : Fin (n + 1) → ℝ → ℝ) : 𝓓'(piecewiseOpenInterval q, ℝ) :=
  ∑ i : Fin n, piecewiseSlopeJump q j i • Distribution.delta (q i.castSucc.succ)

theorem PiecewiseDerivativeData.stateDistribution_apply {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (φ : 𝓓(piecewiseOpenInterval q, ℝ)) :
    h.stateDistribution φ = ∫ x in q 0..q (Fin.last (n + 1)), u x * φ x := rfl

theorem PiecewiseDerivativeData.densityDistribution_apply {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (φ : 𝓓(piecewiseOpenInterval q, ℝ)) :
    h.densityDistribution φ =
      ∑ e : Fin (n + 1), ∫ x in q e.castSucc..q e.succ, g e x * φ x := by
  simp only [PiecewiseDerivativeData.densityDistribution, sum_apply, piecewiseIntervalDistribution_apply]

theorem piecewiseJumpDistribution_apply {n : ℕ} (q : Fin (n + 2) → ℝ)
    (j : Fin (n + 1) → ℝ → ℝ) (φ : 𝓓(piecewiseOpenInterval q, ℝ)) :
    piecewiseJumpDistribution q j φ =
      ∑ i : Fin n, piecewiseSlopeJump q j i * φ (q i.castSucc.succ) := by
  simp only [piecewiseJumpDistribution, sum_apply, smul_apply, Distribution.delta_apply, smul_eq_mul]

theorem PiecewiseDerivativeData.distribution_second {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g) :
    Distribution.lineDerivCLM (k := ⊤) (n := ⊤) (1 : ℝ)
      (Distribution.lineDerivCLM (k := ⊤) (n := ⊤) (1 : ℝ) h.stateDistribution) =
      h.densityDistribution + piecewiseJumpDistribution q j := by
  ext φ
  simp only [Distribution.lineDerivCLM_apply, neg_neg, add_apply,
    PiecewiseDerivativeData.stateDistribution_apply, PiecewiseDerivativeData.densityDistribution_apply,
    piecewiseJumpDistribution_apply]
  have hd := piecewiseTestFunction_derivative (piecewiseOpenInterval q) φ
  have hdd := piecewiseTestFunction_derivative (piecewiseOpenInterval q)
    (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓(piecewiseOpenInterval q, ℝ))
  rw [hd] at hdd
  calc
    _ = ∫ x in q 0..q (Fin.last (n + 1)), u x * deriv (deriv φ) x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [congrFun hdd x]
    _ = _ := by
      rw [intervalSobolev_test_integral (h.node_strictMono.monotone (Fin.zero_le _))
        (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans φ.tsupport_subset))]
      exact h.testFunction_identity φ

end TimeTraps.Analysis
