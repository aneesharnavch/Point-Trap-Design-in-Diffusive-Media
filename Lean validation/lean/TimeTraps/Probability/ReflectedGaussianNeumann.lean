module

public import TimeTraps.Probability.ReflectedGaussianDerivative

@[expose] public section

/-! The actual continuously differentiable reflected Gaussian density
has zero spatial derivative at both endpoints. At zero the two preimage
derivatives cancel termwise. At the other endpoint their absolutely
convergent integer sums agree by shifting the lattice index by one. -/

namespace TimeTraps.Probability

open ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal

theorem reflectedGaussianDensity_neumann_left {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : HasDerivAt (reflectedGaussianDensity L x v) 0 0 := by
  apply (reflectedGaussianDensity_hasDerivAt hL x hv 0).congr_deriv
  simp only [reflectedGaussianDensityDerivative, reflectedGaussianTermDerivative,
    zero_add, sub_zero, sub_self, tsum_zero]

theorem reflectedGaussianDensity_neumann_right {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : HasDerivAt (reflectedGaussianDensity L x v) 0 L := by
  have hp : Summable (fun k : ℤ => gaussianPDFDerivative x v (L + k * (2 * L))) :=
    (gaussianLatticeDerivativeMajorant_summable hL x hv |L|).of_norm_bounded
      (fun k => gaussianPDFDerivative_lattice_bound hL x hv le_rfl k)
  have hm : Summable (fun k : ℤ => gaussianPDFDerivative x v (k * (2 * L) - L)) := by
    have he : (fun k : ℤ => gaussianPDFDerivative x v (k * (2 * L) - L)) =
        fun k : ℤ => gaussianPDFDerivative x v (-L + k * (2 * L)) := by
      funext k
      congr 1
      ring
    rw [he]
    exact (gaussianLatticeDerivativeMajorant_summable hL x hv |-L|).of_norm_bounded
      (fun k => gaussianPDFDerivative_lattice_bound hL x hv le_rfl k)
  have he : (∑' k : ℤ, gaussianPDFDerivative x v (L + k * (2 * L))) =
      ∑' k : ℤ, gaussianPDFDerivative x v (k * (2 * L) - L) := by
    calc
      _ = ∑' k : ℤ, gaussianPDFDerivative x v (((k + 1 : ℤ) : ℝ) * (2 * L) - L) := by
        apply tsum_congr
        intro k
        congr 1
        push_cast
        ring
      _ = _ := (Equiv.addRight (1 : ℤ)).tsum_eq
        (fun k : ℤ => gaussianPDFDerivative x v (k * (2 * L) - L))
  apply (reflectedGaussianDensity_hasDerivAt hL x hv L).congr_deriv
  change (∑' k : ℤ, (gaussianPDFDerivative x v (L + k * (2 * L)) -
    gaussianPDFDerivative x v (k * (2 * L) - L))) = 0
  rw [hp.tsum_sub hm, he, sub_self]

end TimeTraps.Probability
