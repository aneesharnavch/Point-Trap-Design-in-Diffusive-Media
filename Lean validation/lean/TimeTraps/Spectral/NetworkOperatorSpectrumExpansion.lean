module

public import TimeTraps.Spectral.NetworkOperatorSpectrum
public import TimeTraps.Analysis.CompactInverseEigenvalue

@[expose] public section

/-! Unconditional L2, inverse, operator and Parseval expansions for the
actual network eigenbasis. The operator-domain criterion and quadratic
expansion refer to the constructed unbounded operator, not an assumed
spectral definition of its domain. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.operator_eigenvalue_index (P : SpectralNetwork V E)
    {f : GraphL2Product P.geometry} (hf : f ≠ 0) {ev : ℝ}
    (he : (f, ev • f) ∈ P.operator.graph) :
    ∃ i : CompactSpectralIndex P.operatorInverse, i.1⁻¹ = ev :=
  P.operatorCompactPositiveInverse.inverse_eigenvalue_index hf he

theorem SpectralNetwork.eigenbasis_expansion (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      inner ℝ (P.eigenbasis i) f • P.eigenbasis i) f :=
  P.operatorCompactPositiveInverse.hasSum_eigenbasis f

theorem SpectralNetwork.eigenbasis_parseval (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (inner ℝ (P.eigenbasis i) f) ^ 2) (‖f‖ ^ 2) :=
  P.operatorCompactPositiveInverse.hasSum_parseval f

theorem SpectralNetwork.operatorInverse_expansion (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (i.1 * inner ℝ (P.eigenbasis i) f) • P.eigenbasis i) (P.operatorInverse f) :=
  P.operatorCompactPositiveInverse.hasSum_apply f

theorem SpectralNetwork.operator_domain_spectral_iff (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) : f ∈ P.operator.domain ↔
      Summable (fun i : CompactSpectralIndex P.operatorInverse =>
        (i.1⁻¹ * inner ℝ (P.eigenbasis i) f) ^ 2) :=
  P.operatorCompactPositiveInverse.mem_inverse_domain_iff f

theorem SpectralNetwork.operator_expansion (P : SpectralNetwork V E)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (i.1⁻¹ * inner ℝ (P.eigenbasis i) (f : GraphL2Product P.geometry)) • P.eigenbasis i)
        (P.operator f) :=
  P.operatorCompactPositiveInverse.hasSum_inverse f

theorem SpectralNetwork.operator_norm_expansion (P : SpectralNetwork V E)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (i.1⁻¹ * inner ℝ (P.eigenbasis i) (f : GraphL2Product P.geometry)) ^ 2)
        (‖P.operator f‖ ^ 2) :=
  P.operatorCompactPositiveInverse.hasSum_inverse_norm f

theorem SpectralNetwork.operator_quadratic_expansion (P : SpectralNetwork V E)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      i.1⁻¹ * (inner ℝ (P.eigenbasis i) (f : GraphL2Product P.geometry)) ^ 2)
        (inner ℝ (f : GraphL2Product P.geometry) (P.operator f)) := by
  have he : (fun i : CompactSpectralIndex P.operatorInverse =>
      i.1⁻¹ * (inner ℝ (P.eigenbasis i) (f : GraphL2Product P.geometry)) ^ 2) =
      (fun i : CompactSpectralIndex P.operatorInverse =>
        inner ℝ (f : GraphL2Product P.geometry) (P.eigenbasis i) *
          inner ℝ (P.eigenbasis i) (P.operator f)) := by
    funext i
    have hc : inner ℝ (P.eigenbasis i) (P.operator f) =
        i.1⁻¹ * inner ℝ (P.eigenbasis i) (f : GraphL2Product P.geometry) :=
      P.operatorCompactPositiveInverse.inner_eigenbasis_inverse f i
    rw [hc, real_inner_comm (f : GraphL2Product P.geometry)]
    ring
  rw [he]
  exact P.eigenbasis.hasSum_inner_mul_inner (f : GraphL2Product P.geometry) (P.operator f)

theorem SpectralNetwork.operator_physical_quadratic_expansion (P : SpectralNetwork V E)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      i.1⁻¹ * (inner ℝ (P.eigenbasis i) (f : GraphL2Product P.geometry)) ^ 2)
        (P.quadraticForm (P.operatorNodes (P.operatorSolution (P.operator f)))
          (P.operatorRep (P.operatorSolution (P.operator f)))) := by
  have hi : graphSobolevSpaceStateL P.geometry (P.operatorSolution (P.operator f)) = f :=
    inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective f
  rw [← P.operatorForm_self, P.operatorSolution_spec, hi, real_inner_comm]
  exact P.operator_quadratic_expansion f

end TimeTraps.Spectral
