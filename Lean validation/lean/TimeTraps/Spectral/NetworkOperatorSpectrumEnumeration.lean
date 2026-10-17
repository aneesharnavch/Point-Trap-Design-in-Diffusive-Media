module

public import TimeTraps.Spectral.NetworkOperatorSpectrum
public import TimeTraps.Analysis.GeneralIntervalPointEnumeration

@[expose] public section

/-! Infinite dimensionality is derived from the actual L2 space on one
positive-length edge. Projection onto that edge is surjective, so the
complete network eigenbasis admits a sorted natural-number enumeration.
No infinitude premise is added to the original network assumptions. -/

namespace TimeTraps.Spectral

open Set Filter TimeTraps.Analysis
open scoped Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Fintype E] in
theorem SpectralNetwork.operatorL2_not_finiteDimensional (P : SpectralNetwork V E) :
    ¬FiniteDimensional ℝ (GraphL2Product P.geometry) := by
  classical
  intro hf
  let := hf
  let e : E := Classical.choice inferInstance
  have hs : Function.Surjective (graphL2ComponentL P.geometry e) := by
    intro f
    refine ⟨PiLp.single 2 e f, ?_⟩
    change (PiLp.single 2 e f : GraphL2Product P.geometry) e = f
    exact PiLp.single_eq_same (β := fun d : E => IntervalSobolevL2 0 (P.geometry.length d)) 2 e f
  exact intervalL2_not_finiteDimensional (P.length_pos e)
    (FiniteDimensional.of_surjective (graphL2ComponentL P.geometry e).toLinearMap hs)

theorem SpectralNetwork.infinite_spectralIndex (P : SpectralNetwork V E) :
    Infinite (CompactSpectralIndex P.operatorInverse) :=
  P.operatorCompactPositiveInverse.infinite_spectralIndex P.operatorL2_not_finiteDimensional

noncomputable def SpectralNetwork.spectralEnumeration (P : SpectralNetwork V E) :
    ℕ ≃ CompactSpectralIndex P.operatorInverse := by
  letI := P.infinite_spectralIndex
  exact P.operatorCompactPositiveInverse.spectralEnumeration

theorem SpectralNetwork.spectralEnumeration_monotone (P : SpectralNetwork V E) :
    Monotone (fun n => (P.spectralEnumeration n).1⁻¹) := by
  let := P.infinite_spectralIndex
  exact P.operatorCompactPositiveInverse.spectralEnumeration_monotone

theorem SpectralNetwork.spectralEnumeration_tendsto (P : SpectralNetwork V E) :
    Tendsto (fun n => (P.spectralEnumeration n).1⁻¹) atTop atTop := by
  let := P.infinite_spectralIndex
  exact P.operatorCompactPositiveInverse.spectralEnumeration_tendsto

end TimeTraps.Spectral
