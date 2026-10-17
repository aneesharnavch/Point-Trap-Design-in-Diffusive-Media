module

public import TimeTraps.Probability.ReflectedFellerSemigroup
public import TimeTraps.Probability.ReflectedFoldCosine
public import TimeTraps.Analysis.NeumannCosineDensity

@[expose] public section

/-! Exact action of the actual reflected Feller operator on the Neumann
cosine modes. The Gaussian characteristic function is projected to its
real part; no spectral or generator premise is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal

theorem gaussianReal_cosine_integral (x : ℝ) (v : ℝ≥0) (a : ℝ) :
    (∫ y, Real.cos (a * y) ∂gaussianReal x v) =
      Real.exp (-(v : ℝ) * a ^ 2 / 2) * Real.cos (a * x) := by
  let F : ℝ → ℂ := fun y => Complex.exp ((a * y : ℝ) * Complex.I)
  have hi : Integrable F (gaussianReal x v) := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold F; fun_prop)
    exact Filter.Eventually.of_forall (fun y => (Complex.norm_exp_ofReal_mul_I (a * y)).le)
  have hc : (∫ y, F y ∂gaussianReal x v) =
      Complex.exp ((a : ℂ) * (x : ℂ) * Complex.I - (v : ℂ) * (a : ℂ) ^ 2 / 2) := by
    have h := charFun_gaussianReal (μ := x) (v := v) a
    rw [charFun_apply_real] at h
    simpa only [F, Complex.ofReal_mul] using h
  calc
    _ = (∫ y, F y ∂gaussianReal x v).re := by
      have hr := integral_re hi
      change (∫ y, (F y).re ∂gaussianReal x v) = (∫ y, F y ∂gaussianReal x v).re at hr
      have he : (fun y => (F y).re) = (fun y => Real.cos (a * y)) := by
        funext y
        exact Complex.exp_ofReal_mul_I_re _
      rw [he] at hr
      exact hr
    _ = _ := by
      have he : (a : ℂ) * (x : ℂ) * Complex.I - (v : ℂ) * (a : ℂ) ^ 2 / 2 =
          ((-(v : ℝ) * a ^ 2 / 2 : ℝ) : ℂ) + ((a * x : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hc, he, Complex.exp_add]
      rw [← Complex.ofReal_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]

theorem reflectedFellerExtension_cosine (L : ℝ) (hL : 0 < L) (n : ℕ) (x : ℝ) :
    reflectedFellerExtension L hL (neumannCosine L n) x =
      Real.cos (((n : ℝ) * Real.pi / L) * x) := by
  change Real.cos ((((n : ℤ) : ℝ) * Real.pi / L) * reflectedFold L x) = _
  simpa only [Int.cast_natCast] using reflectedFold_cosine L hL n x

theorem reflectedFellerOperator_cosine (L : ℝ) (hL : 0 < L) (v : ℝ≥0) (n : ℕ) :
    reflectedFellerOperator L hL v (neumannCosine L n) =
      Real.exp (-(v : ℝ) * ((n : ℝ) * Real.pi / L) ^ 2 / 2) • neumannCosine L n := by
  ext x
  rw [reflectedFellerOperator_kernel]
  simp_rw [reflectedFellerExtension_cosine]
  rw [reflectedGaussianLaw]
  rw [integral_map (reflectedFold_measurable L).aemeasurable
    (show AEStronglyMeasurable (fun y : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * y))
      ((gaussianReal x.val v).map (reflectedFold L)) from (by fun_prop))]
  simp_rw [reflectedFold_cosine L hL n]
  rw [gaussianReal_cosine_integral]
  rfl

theorem reflectedFellerOperator_finite_cosine (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    reflectedFellerOperator L hL v (∑ n ∈ s, c n • neumannCosine L n) =
      ∑ n ∈ s, (c n * Real.exp (-(v : ℝ) * ((n : ℝ) * Real.pi / L) ^ 2 / 2)) • neumannCosine L n := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul, reflectedFellerOperator_cosine, smul_smul]

theorem reflectedFellerOperator_cosineSpan (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {f : C(Icc (0 : ℝ) L, ℝ)}
    (hf : f ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n))) :
    reflectedFellerOperator L hL v f ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, rfl⟩ := hf
    rw [reflectedFellerOperator_cosine]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

end TimeTraps.Probability
