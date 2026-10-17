module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

/-! A strongly measurable family of actual L² classes admits jointly
measurable scalar approximations with summable L² errors at every
parameter. The scalar evaluations are justified through simple-function
ranges and a measurable choice of approximation index. -/

noncomputable section

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology ENNReal

variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {P : Measure Ω}

theorem simpleFuncL2_jointlyMeasurable (s : SimpleFunc A (Lp ℝ 2 P)) :
    Measurable (fun p : A × Ω => s p.1 p.2) :=
  (s.comp Prod.fst measurable_fst).measurable_bind (fun f p => f p.2)
    (fun f => (Lp.stronglyMeasurable f).measurable.comp measurable_snd)

theorem l2FamilyApproxIndex_exists {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (n : ℕ) (a : A) : ∃ k, ‖hF.approx k a - F a‖ < (1 / 2 : ℝ) ^ n := by
  have ht : Tendsto (fun k => ‖hF.approx k a - F a‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hF.tendsto_approx a).sub_const (F a) |>.norm
  exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n))).exists

def l2FamilyApproxIndex {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (n : ℕ) (a : A) : ℕ :=
  Nat.find (l2FamilyApproxIndex_exists hF n a)

theorem l2FamilyApproxIndex_measurable {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (n : ℕ) : Measurable (l2FamilyApproxIndex hF n) := by
  apply measurable_find
  intro k
  exact measurableSet_lt (((hF.approx k).stronglyMeasurable.sub hF).norm.measurable) measurable_const

def l2FamilyApprox {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (n : ℕ) (a : A) : Lp ℝ 2 P :=
  hF.approx (l2FamilyApproxIndex hF n a) a

theorem l2FamilyApprox_error_lt {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (n : ℕ) (a : A) : ‖l2FamilyApprox hF n a - F a‖ < (1 / 2 : ℝ) ^ n :=
  Nat.find_spec (l2FamilyApproxIndex_exists hF n a)

theorem l2FamilyApprox_jointlyMeasurable {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (n : ℕ) : Measurable (fun p : A × Ω => l2FamilyApprox hF n p.1 p.2) := by
  have hm : Measurable (fun p : (A × Ω) × ℕ => hF.approx p.2 p.1.1 p.1.2) :=
    measurable_from_prod_countable_left (fun k => simpleFuncL2_jointlyMeasurable (hF.approx k))
  exact hm.comp (measurable_id.prodMk ((l2FamilyApproxIndex_measurable hF n).comp measurable_fst))

end TimeTraps.Analysis

end
