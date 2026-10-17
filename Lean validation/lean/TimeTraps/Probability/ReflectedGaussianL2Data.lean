module

public import TimeTraps.Probability.ReflectedGaussianBalance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! The actual stationary reflected-Gaussian joint law gives two
isometric coordinate pullbacks from the original uniform L2 space. No
spectral model or density hypothesis is used in these constructions. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal ProbabilityTheory

abbrev ReflectedUniformL2 (L : ℝ) (hL : 0 < L) := Lp ℝ 2 (reflectedUniformLaw L hL)

def reflectedGaussianJoint (L : ℝ) (hL : 0 < L) (v : ℝ≥0) : Measure (ℝ × ℝ) :=
  (reflectedUniformLaw L hL) ⊗ₘ (reflectedGaussianTransition L v)

instance reflectedGaussianJoint_isProbabilityMeasure (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    IsProbabilityMeasure (reflectedGaussianJoint L hL v) := by
  unfold reflectedGaussianJoint
  infer_instance

theorem reflectedGaussianJoint_fst_preserving (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    MeasurePreserving Prod.fst (reflectedGaussianJoint L hL v) (reflectedUniformLaw L hL) := by
  refine ⟨measurable_fst, ?_⟩
  exact Measure.fst_compProd _ _

theorem reflectedGaussianJoint_snd_preserving (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    MeasurePreserving Prod.snd (reflectedGaussianJoint L hL v) (reflectedUniformLaw L hL) := by
  refine ⟨measurable_snd, ?_⟩
  change ((reflectedUniformLaw L hL) ⊗ₘ (reflectedGaussianTransition L v)).snd = _
  rw [Measure.snd_compProd]
  exact reflectedGaussianTransition_uniform_invariant L hL v

def reflectedGaussianL2Fst (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    ReflectedUniformL2 L hL →ₗᵢ[ℝ] Lp ℝ 2 (reflectedGaussianJoint L hL v) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (reflectedGaussianJoint_fst_preserving L hL v)

def reflectedGaussianL2Snd (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    ReflectedUniformL2 L hL →ₗᵢ[ℝ] Lp ℝ 2 (reflectedGaussianJoint L hL v) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.snd (reflectedGaussianJoint_snd_preserving L hL v)

theorem reflectedGaussianL2Fst_coe (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : ReflectedUniformL2 L hL) :
    (reflectedGaussianL2Fst L hL v f : ℝ × ℝ → ℝ) =ᵐ[reflectedGaussianJoint L hL v]
      fun p => f p.1 :=
  Lp.coeFn_compMeasurePreserving f (reflectedGaussianJoint_fst_preserving L hL v)

theorem reflectedGaussianL2Snd_coe (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : ReflectedUniformL2 L hL) :
    (reflectedGaussianL2Snd L hL v f : ℝ × ℝ → ℝ) =ᵐ[reflectedGaussianJoint L hL v]
      fun p => f p.2 :=
  Lp.coeFn_compMeasurePreserving f (reflectedGaussianJoint_snd_preserving L hL v)

theorem reflectedGaussianJoint_integrable_mul (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f g : ReflectedUniformL2 L hL) :
    Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) (reflectedGaussianJoint L hL v) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (reflectedGaussianL2Fst L hL v f)
    (reflectedGaussianL2Snd L hL v g)).congr
  filter_upwards [reflectedGaussianL2Fst_coe L hL v f,
    reflectedGaussianL2Snd_coe L hL v g] with p hp hq
  simp only [hp, hq, Real.inner_apply]

end TimeTraps.Probability

end
