module

public import TimeTraps.Probability.BrownianIntegralFourthPartition
public import TimeTraps.Probability.BrownianCountableIntegrand

@[expose] public section

/-! The finite partition energy is exactly the ordinary time integral
of the squared dyadic step process. Bounded cutoff energies have an
explicit deterministic bound, including horizon zero. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem brownian_fourth_step_square (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    brownianSquareStepProcess H T n p ^ 2 = brownianSquareStepProcess (fun t ω => H t ω ^ 2) T n p := by
  by_cases hp : p.1 ∈ Ioc 0 T.val
  · obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hp
    rw [brownianSquareStepProcess_cell H T n p.2 i hi,
      brownianSquareStepProcess_cell (fun t ω => H t ω ^ 2) T n p.2 i hi]
  · rw [brownianSquareStepProcess_outside H T n p.2 hp,
      brownianSquareStepProcess_outside (fun t ω => H t ω ^ 2) T n p.2 hp, zero_pow (by norm_num : 2 ≠ 0)]

theorem brownian_fourth_step_time_integrable (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    Integrable (fun r => brownianSquareStepProcess H T n (r, ω)) volume :=
  integrable_finsetSum _ (fun i _ => (brownianIntervalIndicator_integrable _ _).mul_const (H (brownianDyadicGrid T n i.castSucc) ω))

theorem brownian_fourth_step_time_integral (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∫ r, brownianSquareStepProcess H T n (r, ω)) =
      ∑ i : Fin (2 ^ n), ((brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T n i.castSucc).val) *
        H (brownianDyadicGrid T n i.castSucc) ω := by
  unfold brownianSquareStepProcess
  rw [integral_finsetSum _ (fun i _ => (brownianIntervalIndicator_integrable _ _).mul_const (H (brownianDyadicGrid T n i.castSucc) ω))]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ r, brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc) (brownianDyadicGrid T n i.succ) r *
    H (brownianDyadicGrid T n i.castSucc) ω) = _
  have hle : (brownianDyadicGrid T n i.castSucc).val ≤ (brownianDyadicGrid T n i.succ).val :=
    brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)
  rw [integral_mul_const, brownianIntervalIndicator_integral, max_eq_left (sub_nonneg.mpr hle)]

theorem brownian_fourth_step_energy_eq (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∫ r, brownianSquareStepProcess H T n (r, ω) ^ 2) =
      ∑ i : Fin (2 ^ n), ((brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T n i.castSucc).val) *
        H (brownianDyadicGrid T n i.castSucc) ω ^ 2 := by
  simp_rw [brownian_fourth_step_square]
  exact brownian_fourth_step_time_integral (fun t ω => H t ω ^ 2) T n ω

theorem brownian_fourth_cutoff_energy_bound {f : ℝ → ℝ} (hf : Measurable f)
    (M T : ℝ≥0) (hb : ∀ r, |f r| ≤ M.val * brownianIntervalIndicator 0 T r) :
    Integrable (fun r => f r ^ 2) volume ∧
      0 ≤ (∫ r, f r ^ 2) ∧ (∫ r, f r ^ 2) ≤ T.val * M.val ^ 2 := by
  have hbound (r : ℝ) : f r ^ 2 ≤ M.val ^ 2 * brownianIntervalIndicator 0 T r := by
    have hr := hb r
    change |f r| ≤ M.val * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) r at hr
    change f r ^ 2 ≤ M.val ^ 2 * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) r
    by_cases ht : r ∈ Ioc (0 : ℝ) T.val
    · simp only [indicator_of_mem ht, mul_one] at hr ⊢
      have hM := M.coe_nonneg
      nlinarith [sq_abs (f r), abs_nonneg (f r)]
    · simp only [indicator_of_notMem ht, mul_zero] at hr ⊢
      have hz : f r = 0 := abs_nonpos_iff.mp hr
      rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
  have hi : Integrable (fun r => M.val ^ 2 * brownianIntervalIndicator 0 T r) volume :=
    (brownianIntervalIndicator_integrable 0 T).const_mul _
  have hif : Integrable (fun r => f r ^ 2) volume := hi.mono' (hf.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs, abs_sq] using hbound r))
  refine ⟨hif, integral_nonneg (fun r => sq_nonneg _), ?_⟩
  have he : (∫ r, M.val ^ 2 * brownianIntervalIndicator 0 T r) = T.val * M.val ^ 2 := by
    rw [integral_const_mul, brownianIntervalIndicator_integral]
    change M.val ^ 2 * max (T.val - 0) 0 = T.val * M.val ^ 2
    have hmax : max T.val (0 : ℝ) = T.val := max_eq_left T.coe_nonneg
    calc
      _ = M.val ^ 2 * max T.val (0 : ℝ) := by rw [sub_zero]
      _ = M.val ^ 2 * T.val := congrArg (fun z : ℝ => M.val ^ 2 * z) hmax
      _ = _ := mul_comm _ _
  exact (integral_mono hif hi hbound).trans_eq he

end TimeTraps.Probability
