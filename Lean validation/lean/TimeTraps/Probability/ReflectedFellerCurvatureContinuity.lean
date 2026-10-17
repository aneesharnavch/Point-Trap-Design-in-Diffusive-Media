module

public import TimeTraps.Probability.ReflectedFellerSmoothing

@[expose] public section

/-! The positive-time derivative and classical curvature are continuous
in the uniform spatial norm. The proof uses a summable majorant uniformly
on each closed half-line of times bounded away from zero. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped Topology

def reflectedFellerDerivativeCurve (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  ∑' n : ℕ, reflectedFellerHeatTermDerivative L hL D f n t

def reflectedFellerCurvatureCurve (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  D⁻¹ • reflectedFellerDerivativeCurve L hL D f t

theorem reflectedFellerDerivativeCurve_uniform (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun J : Finset ℕ => fun t => ∑ n ∈ J, reflectedFellerHeatTermDerivative L hL D f n t)
      (reflectedFellerDerivativeCurve L hL D f) atTop (Ici δ) :=
  tendstoUniformlyOn_tsum (reflectedFellerHeatTermDerivative_majorant_summable L hL D hD f δ hδ)
    (fun n t ht => reflectedFellerHeatTermDerivative_bound L hL D hD f n δ t ht)

theorem reflectedFellerDerivativeCurve_continuousAt (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    ContinuousAt (reflectedFellerDerivativeCurve L hL D f) t := by
  have hc : ContinuousOn (reflectedFellerDerivativeCurve L hL D f) (Ici (t / 2)) := by
    apply (reflectedFellerDerivativeCurve_uniform L hL D hD f (t / 2) (by positivity)).continuousOn
    apply Frequently.of_forall
    intro J
    apply continuousOn_finsetSum
    intro n _
    have hterm : Continuous (reflectedFellerHeatTerm L hL D f n) :=
      continuous_iff_continuousAt.mpr (fun s => (reflectedFellerHeatTerm_hasDerivAt L hL D f n s).continuousAt)
    exact (hterm.const_smul (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2)).continuousOn
  exact hc.continuousAt (Ici_mem_nhds (by linarith : t / 2 < t))

theorem reflectedFellerDerivativeCurve_continuousOn (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    ContinuousOn (reflectedFellerDerivativeCurve L hL D f) (Ioi 0) :=
  fun t ht => (reflectedFellerDerivativeCurve_continuousAt L hL D hD f t ht).continuousWithinAt

theorem reflectedFellerCurvatureCurve_continuousOn (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    ContinuousOn (reflectedFellerCurvatureCurve L hL D f) (Ioi 0) :=
  (reflectedFellerDerivativeCurve_continuousOn L hL D hD f).const_smul D⁻¹

theorem reflectedFellerCurvatureCurve_scaled (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) :
    D • reflectedFellerCurvatureCurve L hL D f t = reflectedFellerDerivativeCurve L hL D f t := by
  rw [reflectedFellerCurvatureCurve, smul_smul, mul_inv_cancel₀ hD.ne', one_smul]

theorem reflectedFellerCurvatureCurve_representation (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    ∃ F : ReflectedNeumannC2 L,
      F.valueMap = reflectedFellerTimeOperator L hL D t f ∧
      F.curvatureMap = reflectedFellerCurvatureCurve L hL D f t := by
  obtain ⟨F, hf, hg⟩ := reflectedFeller_generator_exists_neumannC2 L hL D hD
    (reflectedFellerTimeOperator L hL D t f) (reflectedFellerDerivativeCurve L hL D f t)
    (reflectedFellerTimeOperator_generator L hL D hD f t ht)
  refine ⟨F, hf, ?_⟩
  have he := congrArg (fun z : C(Icc (0 : ℝ) L, ℝ) => D⁻¹ • z) hg
  change F.curvatureMap = D⁻¹ • reflectedFellerDerivativeCurve L hL D f t
  simpa only [smul_smul, inv_mul_cancel₀ hD.ne', one_smul] using he

end TimeTraps.Probability

end
