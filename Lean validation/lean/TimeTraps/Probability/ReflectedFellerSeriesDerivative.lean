module

public import TimeTraps.Probability.ReflectedFellerSeriesIdentification

@[expose] public section

/-! Positive-time differentiability of the actual Feller trajectory in
the uniform norm. Differentiation is justified by the summable uniform
derivative majorant on a positive time neighborhood. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped Topology NNReal

theorem reflectedFellerHeatSeries_hasDerivAt (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (reflectedFellerHeatSeries L hL D f)
      (∑' n : ℕ, reflectedFellerHeatTermDerivative L hL D f n t) t := by
  have hδ : 0 < t / 2 := by positivity
  have htm : t ∈ Ioi (t / 2) := by change t / 2 < t; linarith
  have hd := hasDerivAt_tsum_of_isPreconnected
    (reflectedFellerHeatTermDerivative_majorant_summable L hL D hD f (t / 2) hδ)
    isOpen_Ioi isPreconnected_Ioi
    (fun n s _ => reflectedFellerHeatTerm_hasDerivAt L hL D f n s)
    (fun n s hs => reflectedFellerHeatTermDerivative_bound L hL D hD f n (t / 2) s hs.le)
    htm (reflectedFellerHeatTerm_summable L hL D hD f t ht) htm
  exact hd.const_add (reflectedFellerMean L hL f • 1)

theorem reflectedFellerTimeOperator_hasDerivAt (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => reflectedFellerTimeOperator L hL D s f)
      (∑' n : ℕ, reflectedFellerHeatTermDerivative L hL D f n t) t := by
  apply (reflectedFellerHeatSeries_hasDerivAt L hL D hD f t ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact (reflectedFellerHeatSeries_eq L hL D hD f s hs).symm

theorem reflectedFellerTimeOperator_add (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    reflectedFellerTimeOperator L hL D (s + t) f =
      reflectedFellerTimeOperator L hL D s (reflectedFellerTimeOperator L hL D t f) := by
  have he : Real.toNNReal (2 * D * (s + t)) =
      Real.toNNReal (2 * D * s) + Real.toNNReal (2 * D * t) := by
    rw [mul_add, Real.toNNReal_add (by positivity) (by positivity)]
  unfold reflectedFellerTimeOperator
  rw [he]
  exact (congrArg (fun A : C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) => A f)
    (reflectedFellerOperator_comp L hL (Real.toNNReal (2 * D * s))
      (Real.toNNReal (2 * D * t)))).symm

theorem reflectedFellerTimeOperator_generator (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ => reflectedFellerTimeOperator L hL D s
      (reflectedFellerTimeOperator L hL D t f))
      (∑' n : ℕ, reflectedFellerHeatTermDerivative L hL D f n t) (Ici 0) 0 := by
  have hd := (reflectedFellerTimeOperator_hasDerivAt L hL D hD f t ht).scomp_of_eq (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).add_const t) (by simp)
  simp only [id_eq, Function.comp_def, one_smul] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro s hs
    exact (reflectedFellerTimeOperator_add L hL D hD.le f s t hs ht.le).symm
  · exact le_refl (0 : ℝ)

end TimeTraps.Probability
