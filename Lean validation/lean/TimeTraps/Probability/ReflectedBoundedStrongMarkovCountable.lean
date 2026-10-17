module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovDeterministic

@[expose] public section

/-! Strong Markov integration against stopping events, first for a
countable range. Each level set belongs to its deterministic past, so
the identity is a sum of the proved deterministic transition laws. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedMarkovObservation_countable_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (h : ℝ≥0) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (hc : (range τ).Countable)
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D h.val f) (τ ω) ω ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedMarkovObservation L hL D x f (τ ω + h) ω ∂brownianCompletedMeasure := by
  let : Countable (range τ) := hc.to_subtype
  let C : range τ → Set BrownianCompletedSample :=
    fun q => A ∩ {ω | (τ ω : WithTop ℝ≥0) = q.val}
  have hC (q : range τ) : MeasurableSet[brownianCompletedFiltration.rightCont q.val] (C q) :=
    (hτ.measurableSet_inter_eq_iff A q.val).mp (hA.inter (hτ.measurableSet_eq' q.val))
  have hCm (q : range τ) : MeasurableSet (C q) :=
    brownianCompletedFiltration.rightCont.le q.val _ (hC q)
  have hCd : Pairwise (fun q r => Disjoint (C q) (C r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro ω hq hr
    apply hqr
    apply Subtype.ext
    exact WithTop.coe_injective (hq.2.symm.trans hr.2)
  have hCu : (⋃ q, C q) = A := by
    ext ω
    simp only [mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      exact hq.1
    · intro hω
      exact ⟨⟨τ ω, ⟨ω, rfl⟩⟩, hω, rfl⟩
  have he (q : range τ) :
      (∫ ω in C q, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D h.val f) (τ ω) ω ∂brownianCompletedMeasure) =
      ∫ ω in C q, reflectedMarkovObservation L hL D x f (τ ω + h) ω ∂brownianCompletedMeasure := by
    have hdet : (∫ ω in C q, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D h.val f) q.val ω ∂brownianCompletedMeasure) =
        ∫ ω in C q, reflectedMarkovObservation L hL D x f (q.val + h) ω ∂brownianCompletedMeasure := by
      convert! reflectedMarkovObservation_rightCont_setIntegral L hL D hD x f
        (show q.val ≤ q.val + h from le_add_of_nonneg_right bot_le) (hC q) using 1
      exact congrArg (fun r : ℝ => ∫ ω in C q, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D r f) q.val ω ∂brownianCompletedMeasure)
          (show h.val = (q.val + h).val - q.val.val from (add_sub_cancel_left _ _).symm)
    calc
      _ = ∫ ω in C q, reflectedMarkovObservation L hL D x
          (reflectedFellerTimeOperator L hL D h.val f) q.val ω ∂brownianCompletedMeasure := by
        apply setIntegral_congr_fun (hCm q)
        intro ω hω
        exact congrArg (fun u => reflectedMarkovObservation L hL D x
          (reflectedFellerTimeOperator L hL D h.val f) u ω) (WithTop.coe_injective hω.2)
      _ = ∫ ω in C q, reflectedMarkovObservation L hL D x f (q.val + h) ω
          ∂brownianCompletedMeasure := hdet
      _ = _ := by
        apply setIntegral_congr_fun (hCm q)
        intro ω hω
        exact (congrArg (fun u => reflectedMarkovObservation L hL D x f (u + h) ω)
          (WithTop.coe_injective hω.2)).symm
  have hi := (reflectedMarkovObservation_stopped_integrable L hL D x
    (reflectedFellerTimeOperator L hL D h.val f) hτ).integrableOn (s := ⋃ q, C q)
  have hj := (reflectedMarkovObservation_stopped_integrable L hL D x f
    (reflectedMarkovStoppingTime_add hτ h)).integrableOn (s := ⋃ q, C q)
  rw [← hCu, integral_iUnion hCm hCd hi, integral_iUnion hCm hCd hj]
  exact tsum_congr he

end TimeTraps.Probability

end
