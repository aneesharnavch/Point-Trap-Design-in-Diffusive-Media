module

public import TimeTraps.Probability.GraphPointLocalTimeSupportData
public import TimeTraps.Analysis.StieltjesLocalSupport

@[expose] public section

/-! The canonical graph local time is constant on every compact time
interval avoiding its target, and locally constant at every noncontact
time. The statement also covers the declared zero exceptional paths. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_eq_of_avoids
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (s t : ℝ≥0) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, p r ≠ a) : P.pointLocalTimePath a p t = P.pointLocalTimePath a p s := by
  by_cases h : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p
  · obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hst)
      ((p.continuous.dist continuous_const).continuousOn)
    have heps : 0 < dist (p u) a := dist_pos.mpr (hp u hu)
    have hn : ∀ᶠ n in atTop, P.localTimeRadius n < dist (p u) a :=
      P.localTimeRadius_tendsto.eventually (Iio_mem_nhds heps)
    have he : (fun n => P.localTimeApproximant a n p t) =ᶠ[atTop]
        (fun n => P.localTimeApproximant a n p s) := by
      filter_upwards [hn] with n hn
      exact P.localTimeApproximant_eq_of_separated a n p s t hst
        (fun r hr => hn.le.trans (hmin hr))
    exact tendsto_nhds_unique (h.eval_tendsto t) ((h.eval_tendsto s).congr' he.symm)
  · have hz := graphLocalTimeCanonicalPath_zero_off (P.localTimeApproximant a) h
    change graphLocalTimeCanonicalPath (P.localTimeApproximant a) p t =
      graphLocalTimeCanonicalPath (P.localTimeApproximant a) p s
    rw [hz]
    rfl

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_locally_constant
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (t : ℝ≥0) (ht : p t ≠ a) :
    ∀ᶠ r in 𝓝 t, P.pointLocalTimePath a p r = P.pointLocalTimePath a p t := by
  have hn : {r | p r ≠ a} ∈ 𝓝 t :=
    ((isClosed_singleton.preimage p.continuous).isOpen_compl).mem_nhds ht
  obtain ⟨s, u, htu, hN, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  filter_upwards [hN] with r hr
  rcases le_total r t with hrt | htr
  · exact (P.pointLocalTimePath_eq_of_avoids a p r t hrt
      (fun z hz => hsub ⟨hr.1.trans hz.1, hz.2.trans htu.2⟩)).symm
  · exact P.pointLocalTimePath_eq_of_avoids a p t r htr
      (fun z hz => hsub ⟨htu.1.trans hz.1, hz.2.trans hr.2⟩)

end TimeTraps.Analysis
