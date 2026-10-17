module

public import TimeTraps.Probability.BrownianBoundedIntegrandProcess
public import TimeTraps.Probability.BrownianSignIntegrandStochastic

@[expose] public section

/-! Finite real linear combinations of the actual sign integrands remain
in the closed Ito-integrand domain. Their representatives and stochastic
integrals are the corresponding finite sums, with only AE evaluation. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {ι : Type*}

noncomputable def brownianFiniteSignIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (s : Finset ι) (c a : ι → ℝ) (T : ℝ≥0) : brownianIntegralSpace B hBm P :=
  ∑ i ∈ s, c i • brownianSignIntegrand hB hBm hjoint (a i) T

theorem brownianFiniteSignIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (s : Finset ι) (c a : ι → ℝ) (T : ℝ≥0) :
    (brownianFiniteSignIntegrand hB hBm hjoint s c a T : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      =ᵐ[volume.prod P] brownianBoundedProcess B (fun z => ∑ i ∈ s, c i * Real.sign (z - a i)) T := by
  have he : (brownianFiniteSignIntegrand hB hBm hjoint s c a T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
      ∑ i ∈ s, c i • (brownianSignIntegrand hB hBm hjoint (a i) T :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    change (brownianIntegralSpace B hBm P).subtype (∑ i ∈ s,
      c i • brownianSignIntegrand hB hBm hjoint (a i) T) = _
    simp only [map_sum, map_smul]
    rfl
  rw [he]
  refine (Lp.coeFn_fun_finsetSum s (fun i => c i •
    (brownianSignIntegrand hB hBm hjoint (a i) T : Lp ℝ 2 ((volume : Measure ℝ).prod P)))).trans ?_
  have hall : ∀ᵐ p ∂volume.prod P, ∀ i ∈ s,
      (c i • (brownianSignIntegrand hB hBm hjoint (a i) T :
        Lp ℝ 2 ((volume : Measure ℝ).prod P))) p =
      c i * ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        Real.sign (B p.1.toNNReal p.2 - a i)) := by
    apply (eventually_all_finset s).mpr
    intro i _
    filter_upwards [Lp.coeFn_smul (c i) (brownianSignIntegrand hB hBm hjoint (a i) T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)), brownianSignIntegrand_coe hB hBm hjoint (a i) T]
      with p hs hi
    rw [hs, Pi.smul_apply, smul_eq_mul, hi]
  filter_upwards [hall] with p hp
  change (∑ i ∈ s, _) = (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
    ∑ i ∈ s, c i * Real.sign (B p.1.toNNReal p.2 - a i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp i hi]
  ring

theorem brownianFiniteSignIntegrand_integral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (s : Finset ι) (c a : ι → ℝ) (T : ℝ≥0) :
    brownianIntegral hB (brownianFiniteSignIntegrand hB hBm hjoint s c a T) =
      ∑ i ∈ s, c i • brownianSignIntegral hB hBm hjoint (a i) T := by
  simp only [brownianFiniteSignIntegrand, map_sum, map_smul, brownianSignIntegral]

theorem brownianFiniteSignFunction_measurable (s : Finset ι) (c a : ι → ℝ) :
    Measurable (fun z : ℝ => ∑ i ∈ s, c i * Real.sign (z - a i)) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact (brownianSign_measurable.comp (measurable_id.sub_const (a i))).const_mul (c i)

end TimeTraps.Probability
