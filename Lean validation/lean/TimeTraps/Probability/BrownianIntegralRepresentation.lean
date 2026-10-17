module

public import TimeTraps.Probability.BrownianIntegralClosure
public import TimeTraps.Probability.BrownianIntegralPredictable

@[expose] public section

/-! Finite elementary-process sums and their representation-independent
stochastic integrals. Equality almost everywhere in time × sample space
implies equality almost surely of the actual finite stochastic sums. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable {I J : Type*} [Fintype I] [Fintype J]

def brownianElementarySum (a : I → BrownianIntegralElementary B hBm P) (p : ℝ × Ω) : ℝ :=
  ∑ i, brownianElementaryProcess (a i).left (a i).right (a i).coefficient p

def brownianElementarySumIntegrand (a : I → BrownianIntegralElementary B hBm P) :
    brownianIntegralSpace B hBm P := ∑ i, brownianIntegralGenerator (a i)

theorem brownianElementarySumIntegrand_coe (a : I → BrownianIntegralElementary B hBm P) :
    (brownianElementarySumIntegrand a : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianElementarySum a := by
  have he : (brownianElementarySumIntegrand a : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
      ∑ i, (a i).processL2 := by
    change (brownianIntegralSpace B hBm P).subtype (∑ i, brownianIntegralGenerator (a i)) = _
    rw [map_sum]
    rfl
  rw [he]
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => (a i).processL2)).trans ?_
  have hall : ∀ᵐ p ∂volume.prod P, ∀ i, (a i).processL2 p =
      brownianElementaryProcess (a i).left (a i).right (a i).coefficient p :=
    ae_all_iff.mpr (fun i => (a i).processL2_coe)
  filter_upwards [hall] with p hp
  exact Finset.sum_congr rfl (fun i _ => hp i)

theorem brownianElementarySum_predictable (a : I → BrownianIntegralElementary B hBm P) :
    IsStronglyPredictable (brownianNaturalFiltration B hBm)
      (fun r ω => brownianElementarySum a (r.val, ω)) := by
  change StronglyMeasurable[(brownianNaturalFiltration B hBm).predictable]
    (fun p : ℝ≥0 × Ω => ∑ i,
      brownianElementaryProcess (a i).left (a i).right (a i).coefficient (p.1.val, p.2))
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact brownianElementaryProcess_predictable hBm (a i).left (a i).right (a i).adapted

theorem brownianIntegral_elementarySum (hB : IsPreBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) :
    brownianIntegral hB (brownianElementarySumIntegrand a) = ∑ i, (a i).integralL2 hB := by
  simp only [brownianElementarySumIntegrand, map_sum, brownianIntegral_generator]

theorem brownianIntegral_elementarySum_ae (hB : IsPreBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) :
    brownianIntegral hB (brownianElementarySumIntegrand a) =ᵐ[P]
      fun ω => ∑ i, (a i).coefficient ω * (B (a i).right ω - B (a i).left ω) := by
  rw [brownianIntegral_elementarySum]
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => (a i).integralL2 hB)).trans ?_
  have hall : ∀ᵐ ω ∂P, ∀ i, (a i).integralL2 hB ω =
      (a i).coefficient ω * (B (a i).right ω - B (a i).left ω) :=
    ae_all_iff.mpr (fun i => (a i).integralL2_coe hB)
  filter_upwards [hall] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

theorem brownianElementarySumIntegrand_eq_of_ae
    (a : I → BrownianIntegralElementary B hBm P) (b : J → BrownianIntegralElementary B hBm P)
    (hab : brownianElementarySum a =ᵐ[volume.prod P] brownianElementarySum b) :
    brownianElementarySumIntegrand a = brownianElementarySumIntegrand b := by
  apply Subtype.ext
  apply Lp.ext
  exact (brownianElementarySumIntegrand_coe a).trans
    (hab.trans (brownianElementarySumIntegrand_coe b).symm)

theorem brownianElementarySums_integral_eq_of_ae (hB : IsPreBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) (b : J → BrownianIntegralElementary B hBm P)
    (hab : brownianElementarySum a =ᵐ[volume.prod P] brownianElementarySum b) :
    (fun ω => ∑ i, (a i).coefficient ω * (B (a i).right ω - B (a i).left ω)) =ᵐ[P]
      fun ω => ∑ j, (b j).coefficient ω * (B (b j).right ω - B (b j).left ω) := by
  have he := brownianElementarySumIntegrand_eq_of_ae a b hab
  have ha := brownianIntegral_elementarySum_ae hB a
  have hb := brownianIntegral_elementarySum_ae hB b
  rw [he] at ha
  exact ha.symm.trans hb

end TimeTraps.Probability

end
