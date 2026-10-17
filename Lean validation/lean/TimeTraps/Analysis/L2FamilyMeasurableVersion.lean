module

public import TimeTraps.Analysis.L2FamilyMeasurableApproximation

@[expose] public section

/-! A jointly measurable representative of a strongly measurable family
of real L² classes. Summable approximation errors prove agreement
almost everywhere in the sample variable for every fixed parameter.
No common exceptional set for all parameters is asserted. -/

noncomputable section

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology ENNReal

variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {P : Measure Ω}

theorem l2FamilyApprox_error_summable {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (a : A) : Summable (fun n => ‖l2FamilyApprox hF n a - F a‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => (l2FamilyApprox_error_lt hF n a).le)
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))

theorem l2FamilyApprox_tendsto_ae {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (a : A) : ∀ᵐ ω ∂P, Tendsto (fun n => l2FamilyApprox hF n a ω) atTop (𝓝 (F a ω)) := by
  have hs : ∀ᵐ ω ∂P, Summable (fun n => ‖(l2FamilyApprox hF n a - F a) ω‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (by norm_num)
      (fun n => Lp.aestronglyMeasurable (l2FamilyApprox hF n a - F a))
    simp only [← Lp.enorm_def]
    exact tsum_enorm_ne_top_iff_summable_norm.mpr (l2FamilyApprox_error_summable hF a)
  have he : ∀ᵐ ω ∂P, ∀ n,
      (l2FamilyApprox hF n a - F a) ω = l2FamilyApprox hF n a ω - F a ω :=
    ae_all_iff.mpr (fun n => Lp.coeFn_sub (l2FamilyApprox hF n a) (F a))
  filter_upwards [hs, he] with ω hω heω
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [heω] using hω.tendsto_atTop_zero

def l2FamilyMeasurableVersion {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (a : A) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => l2FamilyApprox hF n a ω)

theorem l2FamilyMeasurableVersion_jointlyMeasurable {F : A → Lp ℝ 2 P}
    (hF : StronglyMeasurable F) :
    Measurable (fun p : A × Ω => l2FamilyMeasurableVersion hF p.1 p.2) :=
  (StronglyMeasurable.limUnder
    (fun n => (l2FamilyApprox_jointlyMeasurable hF n).stronglyMeasurable)).measurable

theorem l2FamilyMeasurableVersion_ae {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (a : A) : l2FamilyMeasurableVersion hF a =ᵐ[P] F a :=
  (l2FamilyApprox_tendsto_ae hF a).mono (fun _ hω => hω.limUnder_eq)

theorem l2FamilyMeasurableVersion_memLp {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (a : A) : MemLp (l2FamilyMeasurableVersion hF a) 2 P :=
  (memLp_congr_ae (l2FamilyMeasurableVersion_ae hF a)).mpr (Lp.memLp (F a))

theorem l2FamilyMeasurableVersion_toLp {F : A → Lp ℝ 2 P} (hF : StronglyMeasurable F)
    (a : A) : (l2FamilyMeasurableVersion_memLp hF a).toLp (l2FamilyMeasurableVersion hF a) = F a := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (l2FamilyMeasurableVersion_memLp hF a)).trans
    (l2FamilyMeasurableVersion_ae hF a)

end TimeTraps.Analysis

end
