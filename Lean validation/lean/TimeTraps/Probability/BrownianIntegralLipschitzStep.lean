module

public import TimeTraps.Probability.BrownianIntegralLipschitzProcess

@[expose] public section

/-! Actual left-adapted elementary approximations with coefficient
g(B_left). Their pointwise error is exactly the difference of g applied
to the identity-process approximation and its target. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

noncomputable def brownianLipschitzElementary (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    BrownianIntegralElementary B hBm P where
  left := brownianDyadicGrid T n i.castSucc
  right := brownianDyadicGrid T n i.succ
  ordered := brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)
  coefficient := fun ω => g (B (brownianDyadicGrid T n i.castSucc) ω)
  adapted := hg.continuous.comp_stronglyMeasurable (brownianNaturalFiltration_stronglyAdapted B hBm _)
  squareIntegrable := brownianLipschitz_eval_memLp hB hg _

noncomputable def brownianLipschitzStepIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) :
    brownianIntegralSpace B hBm P :=
  brownianElementarySumIntegrand (brownianLipschitzElementary hB hBm hg T n)

noncomputable def brownianLipschitzStepProcess (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ × Ω → ℝ :=
  brownianSquareStepProcess (fun t ω => g (B t ω)) T n

theorem brownianLipschitzStepIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) :
    (brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianLipschitzStepProcess B g T n :=
  brownianElementarySumIntegrand_coe (brownianLipschitzElementary hB hBm hg T n)

theorem brownianLipschitzStep_error_identity (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    brownianLipschitzStepProcess B g T n p - brownianLipschitzProcess B g T p =
      g (brownianSquareStepProcess B T n p) - g (brownianSquareProcess B T p) := by
  rcases p with ⟨r, ω⟩
  by_cases hr : r ∈ Ioc (0 : ℝ) T.val
  · obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hr
    rw [brownianLipschitzStepProcess, brownianLipschitzProcess,
      brownianSquareStepProcess_cell (fun t ω => g (B t ω)) T n ω i hi,
      brownianSquareStepProcess_cell B T n ω i hi]
    simp only [brownianSquareProcess, Set.indicator_of_mem hr, one_mul]
  · rw [brownianLipschitzStepProcess, brownianLipschitzProcess,
      brownianSquareStepProcess_outside (fun t ω => g (B t ω)) T n ω hr,
      brownianSquareStepProcess_outside B T n ω hr]
    simp only [brownianSquareProcess, Set.indicator_of_notMem hr, zero_mul, sub_self]

end TimeTraps.Probability
