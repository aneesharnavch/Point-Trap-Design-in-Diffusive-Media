module

public import TimeTraps.Probability.ReflectedFellerLaplaceExpectation
public import TimeTraps.Probability.ReflectedContinuousDynkinData
public import TimeTraps.Probability.ConditionalIntegral
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! Actual discounted continuation payoffs on the infinite interval
(s,infinity). Bounds depend on the elapsed-time discount and the original
continuous observable; no stopping or killing functional is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

def reflectedDiscountedFuture (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (D α x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioi s.val, Real.exp (-α * (r - s.val)) *
    reflectedContinuousInput L hL D x f (B r.toNNReal ω)

theorem reflectedDiscounted_shift_integral (s : ℝ) (g : ℝ → ℝ) :
    (∫ r in Ioi s, g (r - s)) = ∫ r in Ioi (0 : ℝ), g r := by
  have he := (measurePreserving_add_right (volume : Measure ℝ) s).setIntegral_preimage_emb
    (MeasurableEquiv.addRight s).measurableEmbedding (fun r => g (r - s)) (Ioi s)
  have hs : (fun r : ℝ => r + s) ⁻¹' Ioi s = Ioi 0 := by
    ext r
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  simpa only [hs, add_sub_cancel_right] using he.symm

theorem reflectedDiscounted_exponential_integrable {α : ℝ} (hα : 0 < α) (s : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (-α * (r - s))) (Ioi s) := by
  have he (r : ℝ) : Real.exp (-α * (r - s)) = Real.exp (-α * r) * Real.exp (α * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact (exp_neg_integrableOn_Ioi s hα).mul_const _

theorem reflectedDiscounted_future_joint_integrable [IsFiniteMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {α : ℝ} (hα : 0 < α)
    (f : C(Icc (0 : ℝ) L, ℝ)) (s : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => Real.exp (-α * (p.1 - s.val)) *
      reflectedContinuousInput L hL D x f (B p.1.toNNReal p.2))
      ((volume.restrict (Ioi s.val)).prod P) := by
  have hm : Measurable (fun p : ℝ × Ω => Real.exp (-α * (p.1 - s.val)) *
      reflectedContinuousInput L hL D x f (B p.1.toNNReal p.2)) :=
    (by fun_prop : Measurable (fun p : ℝ × Ω => Real.exp (-α * (p.1 - s.val)))).mul
      ((reflectedContinuousInput_continuous L hL D x f).measurable.comp
        (hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd)))
  apply (((reflectedDiscounted_exponential_integrable hα s.val).mul_const ‖f‖).comp_fst P).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (reflectedContinuousInput_bound L hL D x f _) (Real.exp_pos _).le

theorem reflectedDiscountedFuture_integrable [IsFiniteMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {α : ℝ} (hα : 0 < α)
    (f : C(Icc (0 : ℝ) L, ℝ)) (s : ℝ≥0) :
    Integrable (reflectedDiscountedFuture B L hL D α x f s) P :=
  (reflectedDiscounted_future_joint_integrable B hjoint L hL D x hα f s).integral_prod_right

end TimeTraps.Probability

end
