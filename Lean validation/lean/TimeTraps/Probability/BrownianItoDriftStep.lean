module

public import TimeTraps.Probability.BrownianItoDriftProcess

@[expose] public section

/-! Actual left dyadic time sums are the ordinary time integrals of
the already constructed adapted step processes. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

noncomputable def brownianItoDriftSum (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (2 ^ n), ((brownianDyadicGrid T n i.succ).val -
    (brownianDyadicGrid T n i.castSucc).val) * g (B (brownianDyadicGrid T n i.castSucc) ω)

theorem brownianItoDriftSum_step_integrable (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    Integrable (fun s => brownianLipschitzStepProcess B g T n (s, ω)) volume := by
  change Integrable (fun s => ∑ i : Fin (2 ^ n), brownianIntervalIndicator
    (brownianDyadicGrid T n i.castSucc) (brownianDyadicGrid T n i.succ) s *
      g (B (brownianDyadicGrid T n i.castSucc) ω)) volume
  exact integrable_finsetSum Finset.univ (fun (i : Fin (2 ^ n)) _ =>
    (brownianIntervalIndicator_integrable (brownianDyadicGrid T n i.castSucc)
      (brownianDyadicGrid T n i.succ)).mul_const (g (B (brownianDyadicGrid T n i.castSucc) ω)))

theorem brownianItoDriftSum_step_integral (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∫ s in (0 : ℝ)..T.val, brownianLipschitzStepProcess B g T n (s, ω)) =
      brownianItoDriftSum B g T n ω := by
  calc
    _ = ∫ s in Ioc (0 : ℝ) T.val, brownianLipschitzStepProcess B g T n (s, ω) :=
      intervalIntegral.integral_of_le T.coe_nonneg
    _ = ∫ s, brownianLipschitzStepProcess B g T n (s, ω) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs =>
        brownianSquareStepProcess_outside (fun t ω => g (B t ω)) T n ω hs)
    _ = _ := by
      change (∫ s, ∑ i : Fin (2 ^ n), brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
        (brownianDyadicGrid T n i.succ) s * g (B (brownianDyadicGrid T n i.castSucc) ω)) = _
      rw [integral_finsetSum _ (fun (i : Fin (2 ^ n)) _ =>
        (brownianIntervalIndicator_integrable (brownianDyadicGrid T n i.castSucc)
          (brownianDyadicGrid T n i.succ)).mul_const (g (B (brownianDyadicGrid T n i.castSucc) ω)))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_mul_const, brownianIntervalIndicator_integral]
      have hgap : (brownianDyadicGrid T n i.castSucc).val ≤ (brownianDyadicGrid T n i.succ).val :=
        brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)
      exact congrArg (fun r : ℝ => r * g (B (brownianDyadicGrid T n i.castSucc) ω))
        (max_eq_left (sub_nonneg.mpr hgap))

theorem brownianItoDriftSum_measurable (hBm : ∀ t, Measurable (B t))
    (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) : Measurable (brownianItoDriftSum B g T n) :=
  Finset.measurable_sum _ (fun (i : Fin (2 ^ n)) _ =>
    (hg.continuous.measurable.comp (hBm (brownianDyadicGrid T n i.castSucc))).const_mul _)

theorem brownianItoDriftSum_memLp (hB : IsPreBrownianReal B P)
    (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) : MemLp (brownianItoDriftSum B g T n) 2 P :=
  memLp_finsetSum _ (fun (i : Fin (2 ^ n)) _ =>
    (brownianLipschitz_eval_memLp hB hg (brownianDyadicGrid T n i.castSucc)).const_mul _)

noncomputable def brownianItoDriftSumL2 (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ)
    (hSum : MemLp (brownianItoDriftSum B g T n) 2 P) : Lp ℝ 2 P :=
  hSum.toLp (brownianItoDriftSum B g T n)

theorem brownianItoDriftSumL2_coe (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ)
    (hSum : MemLp (brownianItoDriftSum B g T n) 2 P) :
    brownianItoDriftSumL2 B g T n hSum =ᵐ[P] brownianItoDriftSum B g T n := hSum.coeFn_toLp

theorem brownianItoDriftSum_zero (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (n : ℕ) (ω : Ω) :
    brownianItoDriftSum B g 0 n ω = 0 := by simp [brownianItoDriftSum, brownianDyadicGrid]

end TimeTraps.Probability
