module

public import TimeTraps.Probability.ReflectedCosineIntegrals
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-! The normalized Neumann cosines in the actual uniform L2 space:
constant mode one, and sqrt(2) times every positive-index cosine. Their
orthonormality and exact reflected-Gaussian eigenaction include n = 0. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def reflectedCosineScale (n : ℕ) : ℝ := if n = 0 then 1 else Real.sqrt 2

def reflectedL2Cosine (L : ℝ) (hL : 0 < L) (n : ℕ) : ReflectedUniformL2 L hL :=
  reflectedCosineScale n • reflectedFellerToL2 L hL (neumannCosine L n)

theorem reflectedCosineScale_pos (n : ℕ) : 0 < reflectedCosineScale n := by
  unfold reflectedCosineScale
  split_ifs <;> positivity

theorem reflectedL2Cosine_coe (L : ℝ) (hL : 0 < L) (n : ℕ) :
    (reflectedL2Cosine L hL n : ℝ → ℝ) =ᵐ[reflectedUniformLaw L hL]
      fun x => reflectedCosineScale n * Real.cos (((n : ℝ) * Real.pi / L) * x) := by
  filter_upwards [Lp.coeFn_smul (reflectedCosineScale n)
    (reflectedFellerToL2 L hL (neumannCosine L n)),
    reflectedFellerToL2_coe L hL (neumannCosine L n)] with x hx hy
  change ((reflectedCosineScale n • reflectedFellerToL2 L hL (neumannCosine L n) :
    ReflectedUniformL2 L hL) : ℝ → ℝ) x = _
  rw [hx]
  change reflectedCosineScale n * (reflectedFellerToL2 L hL (neumannCosine L n)) x = _
  rw [hy, reflectedFellerExtension_cosine]

theorem reflectedL2Cosine_zero (L : ℝ) (hL : 0 < L) :
    reflectedL2Cosine L hL 0 = reflectedFellerToL2 L hL 1 := by
  norm_num [reflectedL2Cosine, reflectedCosineScale, neumannCosine_zero]

theorem reflectedL2Cosine_orthonormal (L : ℝ) (hL : 0 < L) :
    Orthonormal ℝ (reflectedL2Cosine L hL) := by
  rw [orthonormal_iff_ite]
  intro m n
  unfold reflectedL2Cosine
  rw [real_inner_smul_left, real_inner_smul_right, reflectedFellerToL2_cosine_inner]
  by_cases hmn : m = n
  · subst m
    by_cases hn : n = 0
    · norm_num [reflectedCosineScale, hn]
    · simp only [if_neg hn, reflectedCosineScale, ← mul_assoc]
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
  · simp [hmn]

theorem reflectedGaussianL2Operator_cosine (L : ℝ) (hL : 0 < L) (v : ℝ≥0) (n : ℕ) :
    reflectedGaussianL2Operator L hL v (reflectedL2Cosine L hL n) =
      Real.exp (-(v : ℝ) * ((n : ℝ) * Real.pi / L) ^ 2 / 2) • reflectedL2Cosine L hL n := by
  unfold reflectedL2Cosine
  rw [map_smul, reflectedGaussianL2Operator_feller, reflectedFellerOperator_cosine, map_smul]
  exact smul_comm _ _ _

end TimeTraps.Probability

end
