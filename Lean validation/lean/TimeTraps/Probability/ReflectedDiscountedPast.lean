module

public import TimeTraps.Probability.ReflectedDiscountedData
public import TimeTraps.Probability.BrownianItoDriftContinuousAdapted

@[expose] public section

/-! The actual discounted past integral is measurable up to null sets
in the original raw Brownian past. Adapted finite time sums converge on
the proved continuity event; their limit supplies the raw representative. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedDiscountedPast (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (D α x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..T.val, Real.exp (-α * r) * reflectedContinuousInput L hL D x f (B r.toNNReal ω)

theorem reflectedDiscountedPast_aestronglyMeasurable (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm T]
      (reflectedDiscountedPast B L hL D α x f T) P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => Real.exp (-α * t.val) * reflectedContinuousInput L hL D x f (B t ω)
  have hb (t : ℝ≥0) (ω : Ω) : |X t ω| ≤ ‖f‖ := by
    dsimp only [X]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (reflectedContinuousInput_bound L hL D x f _) (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left (norm_nonneg f) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) t.coe_nonneg)))
  have hm (n : ℕ) : StronglyMeasurable[brownianNaturalFiltration B hBm T] (brownianItoDriftSum X id T n) := by
    unfold brownianItoDriftSum
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    have ht : brownianDyadicGrid T n i.castSucc ≤ T := by
      simpa only [brownianDyadicGrid_last] using brownianDyadicGrid_monotone T n (Fin.le_last i.castSucc)
    exact (((reflectedContinuousInput_continuous L hL D x f).comp_stronglyMeasurable
      ((brownianNaturalFiltration_stronglyAdapted B hBm _).mono
        ((brownianNaturalFiltration B hBm).mono ht))).const_mul _).const_mul _
  have hlim (ω : Ω) (hpath : Continuous (fun t => B t ω)) :
      Tendsto (fun n => brownianItoDriftSum X id T n ω) atTop
        (𝓝 (reflectedDiscountedPast B L hL D α x f T ω)) := by
    have hc : Continuous (fun t => X t ω) :=
      (by fun_prop : Continuous (fun t : ℝ≥0 => Real.exp (-α * t.val))).mul
        ((reflectedContinuousInput_continuous L hL D x f).comp hpath)
    have hd := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) T.val))
      (F := fun n r => brownianLipschitzStepProcess X id T n (r, ω))
      (f := fun r => X r.toNNReal ω) (fun _ => ‖f‖)
      (fun n => (brownianItoDriftSum_step_integrable X id T n ω).aestronglyMeasurable.restrict)
      (integrable_const ‖f‖) (fun n => ?_) ?_
    · have he (n : ℕ) : (∫ r in Ioc (0 : ℝ) T.val, brownianLipschitzStepProcess X id T n (r, ω)) =
          brownianItoDriftSum X id T n ω :=
        (intervalIntegral.integral_of_le T.coe_nonneg).symm.trans (brownianItoDriftSum_step_integral X id T n ω)
      have hp : (∫ r in Ioc (0 : ℝ) T.val, X r.toNNReal ω) = reflectedDiscountedPast B L hL D α x f T ω := by
        calc
          _ = ∫ r in Ioc (0 : ℝ) T.val, Real.exp (-α * r) *
              reflectedContinuousInput L hL D x f (B r.toNNReal ω) := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
            dsimp only [X]
            exact congrArg (fun z : ℝ => Real.exp (-α * z) *
              reflectedContinuousInput L hL D x f (B r.toNNReal ω)) (Real.coe_toNNReal r hr.1.le)
          _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm
      simpa only [he, hp] using hd
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hr
      rw [brownianLipschitzStepProcess, brownianSquareStepProcess_cell _ T n ω i hi, Real.norm_eq_abs]
      exact hb _ ω
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have ht := brownianSquareStepProcess_tendsto_at X T (r, ω) (fun _ => hc.continuousAt)
      simpa only [brownianLipschitzStepProcess, brownianSquareProcess, Set.indicator_of_mem hr, one_mul, id_eq] using ht
  let V (ω : Ω) : ℝ := limUnder atTop (fun n => brownianItoDriftSum X id T n ω)
  refine ⟨V, ?_, ?_⟩
  · let : MeasurableSpace Ω := brownianNaturalFiltration B hBm T
    exact StronglyMeasurable.limUnder hm
  · filter_upwards [hB.cont] with ω hω
    exact (hlim ω hω).limUnder_eq.symm

theorem reflectedDiscountedPast_integrable [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {α : ℝ} (hα : 0 < α)
    (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    Integrable (reflectedDiscountedPast B L hL D α x f T) P := by
  have hi := reflectedDiscounted_future_joint_integrable (P := P) B hjoint L hL D x hα f 0
  have hz : (0 : ℝ≥0).val = 0 := rfl
  simp only [hz, sub_zero] at hi
  have hj : Integrable (fun p : ℝ × Ω => Real.exp (-α * p.1) *
      reflectedContinuousInput L hL D x f (B p.1.toNNReal p.2))
      ((volume.restrict (Ioc 0 T.val)).prod P) := by
    exact hi.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume
        (show Ioc (0 : ℝ) T.val ⊆ Ioi 0 from Ioc_subset_Ioi_self)) le_rfl)
  have he : reflectedDiscountedPast B L hL D α x f T =
      (fun ω => ∫ r in Ioc (0 : ℝ) T.val, Real.exp (-α * r) * reflectedContinuousInput L hL D x f (B r.toNNReal ω)) :=
    funext (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
  rw [he]
  exact hj.integral_prod_right

end TimeTraps.Probability

end
