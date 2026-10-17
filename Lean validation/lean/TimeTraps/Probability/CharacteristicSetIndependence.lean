module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! Characteristic tests against every event in a sigma algebra imply
independence from that entire sigma algebra. The proof compares the
actual restricted pushforward and the scaled full law using uniqueness
of finite-measure characteristic functions. The variable need only be
almost everywhere measurable; no Gaussian law is required. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem map_restrict_eq_smul_of_characteristic_tests [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) (A : Set Ω)
    (hchar : ∀ u : ℝ,
      (∫ ω in A, Complex.exp ((u * X ω : ℝ) * Complex.I) ∂P) =
        (P.real A : ℂ) * ∫ ω, Complex.exp ((u * X ω : ℝ) * Complex.I) ∂P) :
    (P.restrict A).map X = P A • P.map X := by
  let : IsFiniteMeasure (P A • P.map X) := Measure.smul_finite _ (measure_ne_top P A)
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_apply_real, charFun_apply_real, integral_smul_measure,
    integral_map hX.restrict (by fun_prop), integral_map hX (by fun_prop)]
  simpa only [Complex.ofReal_mul, measureReal_def, Complex.real_smul] using hchar u

theorem indep_comap_of_characteristic_set_tests [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ u : ℝ,
      (∫ ω in A, Complex.exp ((u * X ω : ℝ) * Complex.I) ∂P) =
        (P.real A : ℂ) * ∫ ω, Complex.exp ((u * X ω : ℝ) * Complex.I) ∂P) :
    Indep (MeasurableSpace.comap X (borel ℝ)) m P := by
  apply (Indep_iff _ _ _).mpr
  rintro S A ⟨B, hB, rfl⟩ hA
  have he := congrArg (fun μ : Measure ℝ => μ B)
    (map_restrict_eq_smul_of_characteristic_tests hX A (hchar A hA))
  rw [Measure.map_apply_of_aemeasurable hX.restrict hB,
    Measure.restrict_apply' (hm A hA), Measure.smul_apply,
    Measure.map_apply_of_aemeasurable hX hB] at he
  exact he.trans (mul_comm _ _)

theorem indep_comap_of_characteristic_multiplier_tests [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hchar : ∀ Z : Ω → ℂ, StronglyMeasurable[m] Z → Integrable Z P → ∀ u : ℝ,
      (∫ ω, Z ω * Complex.exp ((u * X ω : ℝ) * Complex.I) ∂P) =
        (∫ ω, Z ω ∂P) * ∫ ω, Complex.exp ((u * X ω : ℝ) * Complex.I) ∂P) :
    Indep (MeasurableSpace.comap X (borel ℝ)) m P := by
  apply indep_comap_of_characteristic_set_tests hm hX
  intro A hA u
  have hAm : MeasurableSet[mΩ] A := hm A hA
  have he := hchar (A.indicator (fun _ => (1 : ℂ)))
    (stronglyMeasurable_const.indicator hA) ((integrable_const (1 : ℂ)).indicator hAm) u
  have hf : (fun ω => A.indicator (fun _ => (1 : ℂ)) ω *
      Complex.exp ((u * X ω : ℝ) * Complex.I)) =
      A.indicator (fun ω => Complex.exp ((u * X ω : ℝ) * Complex.I)) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, one_mul]
    · simp only [indicator_of_notMem hω, zero_mul]
  rw [hf, integral_indicator hAm, integral_indicator_const (1 : ℂ) hAm] at he
  simpa only [Complex.real_smul, mul_one] using he

end TimeTraps.Probability
