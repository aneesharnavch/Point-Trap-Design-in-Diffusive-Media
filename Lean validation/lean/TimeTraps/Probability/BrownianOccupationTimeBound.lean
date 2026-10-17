module

public import TimeTraps.Probability.BrownianItoDriftProcess

@[expose] public section

/-! The genuine ordinary time integral of a bounded measurable function
of the process is measurable and lies in L2 on every finite horizon.
These bounds require joint measurability, not a Brownian-law assumption. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianItoDrift_bounded_measurable {g : ℝ → ℝ} (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (brownianItoDrift B g T) := by
  have hm : Measurable (fun p : ℝ × Ω => g (B p.1.toNNReal p.2)) :=
    hg.comp (hjoint.comp
      ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd))
  have he : brownianItoDrift B g T = (fun ω => ∫ s in Ioc (0 : ℝ) T.val, g (B s.toNNReal ω)) :=
    funext (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
  rw [he]
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) T.val))).measurable

theorem brownianItoDrift_bounded_intervalIntegrable {g : ℝ → ℝ} (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) (ω : Ω) :
    IntervalIntegrable (fun s => g (B s.toNNReal ω)) volume 0 T.val := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  have hm : Measurable (fun s : ℝ => g (B s.toNNReal ω)) :=
    hg.comp (hjoint.comp ((by fun_prop : Measurable (fun s : ℝ => s.toNNReal)).prodMk measurable_const))
  exact (integrable_const M).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hb (B s.toNNReal ω))

theorem brownianItoDrift_bounded_abs {g : ℝ → ℝ} {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) (ω : Ω) :
    |brownianItoDrift B g T ω| ≤ T.val * M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T.val) (f := fun s => g (B s.toNNReal ω))
    (fun s _ => by simpa only [Real.norm_eq_abs] using hb (B s.toNNReal ω))
  simpa [brownianItoDrift, Real.norm_eq_abs, abs_of_nonneg T.coe_nonneg, mul_comm] using h

theorem brownianItoDrift_bounded_memLp [IsFiniteMeasure P] {g : ℝ → ℝ} (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    MemLp (brownianItoDrift B g T) 2 P := by
  apply MemLp.of_bound (brownianItoDrift_bounded_measurable hg hjoint T).aestronglyMeasurable (T.val * M)
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using brownianItoDrift_bounded_abs hb T ω

end TimeTraps.Probability
