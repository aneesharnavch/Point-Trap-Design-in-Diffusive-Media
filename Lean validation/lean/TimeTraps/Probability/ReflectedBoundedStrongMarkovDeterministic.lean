module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovData

@[expose] public section

/-! The already derived Gaussian reflected transition law survives the
explicit completion. Its extension to the right-continuous filtration
is a dominated limit from later conditioning times. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedContinuousInput_brownian_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) :
    Integrable (fun ω => reflectedContinuousInput L hL D x f (brownianDyadicPath t ω))
      brownianDyadicMeasure := by
  apply (integrable_const ‖f‖).mono'
    ((reflectedContinuousInput_continuous L hL D x f).measurable.comp
      (brownianDyadicPath_measurable t)).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => reflectedContinuousInput_bound L hL D x f _)

theorem reflectedMarkovObservation_completed_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[brownianCompletedFiltration s] A) :
    (∫ ω in A, reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D (t.val - s.val) f) s ω ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedMarkovObservation L hL D x f t ω ∂brownianCompletedMeasure := by
  obtain ⟨C, hC, he⟩ := hA
  have hCm := brownianFiltration.le s C hC
  have hec : A =ᵐ[brownianCompletedMeasure] C := he
  rw [setIntegral_congr_set hec, setIntegral_congr_set hec]
  have htransfer (g : C(Icc (0 : ℝ) L, ℝ)) (u : ℝ≥0) :
      (∫ ω in C, reflectedMarkovObservation L hL D x g u ω ∂brownianCompletedMeasure) =
      ∫ ω in C, reflectedContinuousInput L hL D x g (brownianDyadicPath u ω)
        ∂brownianDyadicMeasure := by
    calc
      _ = ∫ ω in C, reflectedContinuousInput L hL D x g (brownianDyadicPath u ω)
            ∂brownianCompletedMeasure := by
        apply integral_congr_ae
        filter_upwards [reflectedMarkovBrownianPath_ae_all.filter_mono ae_restrict_le] with ω hω
        exact congrArg (reflectedContinuousInput L hL D x g) (hω u)
      _ = _ := completedMeasure_setIntegral brownianDyadicMeasure
        (reflectedContinuousInput_brownian_integrable L hL D x g u).aestronglyMeasurable hCm
  rw [htransfer, htransfer]
  have hc := reflectedContinuousInput_condExp brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable L hL D hD x f hst
  exact (integral_congr_ae (hc.symm.filter_mono ae_restrict_le)).trans
    (setIntegral_condExp (brownianFiltration.le s)
      (reflectedContinuousInput_brownian_integrable L hL D x f t) hC)

theorem reflectedMarkovObservation_time_continuous
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    (t : ℝ≥0) (ω : BrownianCompletedSample) :
    Continuous (fun s : ℝ≥0 => reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D (t.val - s.val) f) s ω) := by
  have hg : Continuous (fun s : ℝ≥0 =>
      (t.val - s.val, reflectedMarkovBrownianPath s ω)) :=
    (continuous_const.sub NNReal.continuous_coe).prodMk
      (reflectedMarkovBrownianPath_continuous ω)
  simpa only [reflectedMarkovObservation, Function.comp_def] using
    (reflectedContinuousInput_time_continuous L hL D x f).comp hg

theorem reflectedMarkovObservation_rightCont_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set BrownianCompletedSample}
    (hA : MeasurableSet[brownianCompletedFiltration.rightCont s] A) :
    (∫ ω in A, reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D (t.val - s.val) f) s ω ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedMarkovObservation L hL D x f t ω ∂brownianCompletedMeasure := by
  rcases hst.eq_or_lt with rfl | hst
  · simp only [sub_self, reflectedFellerTimeOperator, mul_zero, Real.toNNReal_zero,
      reflectedFellerOperator_zero]
  have he : ∀ᶠ u in 𝓝[>] s,
      (∫ ω in A, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D (t.val - u.val) f) u ω ∂brownianCompletedMeasure) =
        ∫ ω in A, reflectedMarkovObservation L hL D x f t ω ∂brownianCompletedMeasure := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hst)] with u hsu hut
    have hle : brownianCompletedFiltration.rightCont s ≤ brownianCompletedFiltration u := by
      rw [Filtration.rightCont_eq]
      exact iInf_le_of_le u (iInf_le _ hsu)
    exact reflectedMarkovObservation_completed_setIntegral L hL D hD x f hut (hle A hA)
  have hlim : Tendsto (fun u : ℝ≥0 => ∫ ω in A, reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D (t.val - u.val) f) u ω ∂brownianCompletedMeasure)
      (𝓝[>] s) (𝓝 (∫ ω in A, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D (t.val - s.val) f) s ω ∂brownianCompletedMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : BrownianCompletedSample => ‖f‖)
    · exact Eventually.of_forall (fun u =>
        ((reflectedMarkovObservation_stronglyAdapted L hL D x _ u).mono
          (brownianCompletedFiltration.rightCont.le u)).aestronglyMeasurable.restrict)
    · exact Eventually.of_forall (fun u => Eventually.of_forall (fun ω =>
        reflectedContinuousInput_time_bound L hL D x f _ _))
    · exact integrable_const _
    · exact Eventually.of_forall (fun ω =>
        (reflectedMarkovObservation_time_continuous L hL D x f t ω).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm)))

end TimeTraps.Probability

end
