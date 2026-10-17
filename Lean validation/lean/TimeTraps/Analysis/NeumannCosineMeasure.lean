module

public import TimeTraps.Analysis.NeumannCosineDensity
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Natural cosine moments determine every finite Borel measure on the
closed interval. The real-line version assumes only almost-everywhere
confinement, so no density or absence of endpoint atoms is required. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped ENNReal

theorem neumannCosine_integral_eq (L : ℝ) (hL : 0 < L)
    (μ ν : Measure (Icc (0 : ℝ) L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcos : ∀ n : ℕ, (∫ x, neumannCosine L n x ∂μ) = ∫ x, neumannCosine L n x ∂ν)
    (f : C(Icc (0 : ℝ) L, ℝ)) : (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  have hi (η : Measure (Icc (0 : ℝ) L)) [IsFiniteMeasure η]
      (g : C(Icc (0 : ℝ) L, ℝ)) : Integrable g η :=
    (BoundedContinuousFunction.mkOfCompact g).integrable η
  have hc (η : Measure (Icc (0 : ℝ) L)) [IsFiniteMeasure η] :
      Continuous (fun g : C(Icc (0 : ℝ) L, ℝ) => ∫ x, g x ∂η) := by
    have hh : Continuous (fun g : C(Icc (0 : ℝ) L, ℝ) =>
        ∫ x, (ContinuousMap.toLp 1 η ℝ g) x ∂η) :=
      continuous_integral.comp (ContinuousMap.toLp 1 η ℝ).continuous
    apply hh.congr
    intro g
    exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) η g)
  have hs : ∀ g ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n)),
      (∫ x, g x ∂μ) = ∫ x, g x ∂ν := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n, rfl⟩ := hg
      exact hcos n
    | zero => simp
    | add g k _ _ hg hk =>
      simp only [ContinuousMap.add_apply, integral_add (hi μ g) (hi μ k),
        integral_add (hi ν g) (hi ν k), hg, hk]
    | smul r g _ hg =>
      simp only [ContinuousMap.smul_apply, integral_smul, hg]
  have hclosed : IsClosed {g : C(Icc (0 : ℝ) L, ℝ) | (∫ x, g x ∂μ) = ∫ x, g x ∂ν} :=
    isClosed_eq (hc μ) (hc ν)
  have ha : (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) ⊆
      {g | (∫ x, g x ∂μ) = ∫ x, g x ∂ν} := by
    intro g hg
    apply hs g
    rw [← neumannCosineSpan_eq_natSpan]
    exact hg
  apply closure_minimal ha hclosed
  change f ∈ (neumannCosineAlgebra L).topologicalClosure
  rw [neumannCosineAlgebra_dense L hL]
  trivial

theorem neumannCosine_measure_ext (L : ℝ) (hL : 0 < L)
    (μ ν : Measure (Icc (0 : ℝ) L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcos : ∀ n : ℕ, (∫ x, neumannCosine L n x ∂μ) = ∫ x, neumannCosine L n x ∂ν) :
    μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact neumannCosine_integral_eq L hL μ ν hcos f.toContinuousMap

theorem neumannCosine_measure_ext_supported (L : ℝ) (hL : 0 < L)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc 0 L) (hν : ∀ᵐ x ∂ν, x ∈ Icc 0 L)
    (hcos : ∀ n : ℕ, (∫ x, Real.cos (((n : ℝ) * Real.pi / L) * x) ∂μ) =
      ∫ x, Real.cos (((n : ℝ) * Real.pi / L) * x) ∂ν) : μ = ν := by
  have he : μ.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) =
      ν.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) := by
    apply neumannCosine_measure_ext L hL
    intro n
    change (∫ x : Icc (0 : ℝ) L, Real.cos (((n : ℝ) * Real.pi / L) * x.val)
        ∂μ.comap Subtype.val) =
      ∫ x : Icc (0 : ℝ) L, Real.cos (((n : ℝ) * Real.pi / L) * x.val) ∂ν.comap Subtype.val
    rw [integral_subtype_comap (μ := μ) (s := Icc (0 : ℝ) L) measurableSet_Icc
      (fun x : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * x)),
      integral_subtype_comap (μ := ν) (s := Icc (0 : ℝ) L) measurableSet_Icc
      (fun x : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * x)),
      Measure.restrict_eq_self_of_ae_mem hμ, Measure.restrict_eq_self_of_ae_mem hν]
    exact hcos n
  have hm := congrArg (fun η : Measure (Icc (0 : ℝ) L) => η.map Subtype.val) he
  rwa [map_comap_subtype_coe measurableSet_Icc, map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem hμ, Measure.restrict_eq_self_of_ae_mem hν] at hm

end TimeTraps.Analysis
