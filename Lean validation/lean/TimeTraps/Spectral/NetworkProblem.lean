module

public import TimeTraps.Graph.WeakState

@[expose] public section

/-! Independent homogeneous spectral data and the full metric-network Rayleigh class.
The circle will be instantiated as a cyclic network, including its wrap edge. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

structure SpectralNetwork (V E : Type*) where
  tail : E → V
  head : E → V
  length : E → ℝ
  length_pos : ∀ e, 0 < length e
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : V → ℝ
  strength_pos : ∀ v, 0 < strength v
  connected : IncidenceConnected tail head

variable {V E : Type*}

def SpectralNetwork.geometry (P : SpectralNetwork V E) : MetricGraph V E where
  tail := P.tail
  head := P.head
  length := P.length
  length_pos := P.length_pos
  conductance := fun _ _ => P.diffusivity
  source := fun _ _ => 1
  conductance_continuous := fun _ => continuousOn_const
  source_continuous := fun _ => continuousOn_const
  conductance_pos := fun _ _ _ => P.diffusivity_pos
  source_pos := fun _ _ _ => zero_lt_one
  connected := P.connected

noncomputable def SpectralNetwork.totalLength [Fintype E] (P : SpectralNetwork V E) : ℝ :=
  ∑ e, P.length e

noncomputable def SpectralNetwork.totalStrength [Fintype V] (P : SpectralNetwork V E) : ℝ :=
  ∑ v, P.strength v

noncomputable def SpectralNetwork.quadraticForm [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) (U : V → ℝ) (u : E → ℝ → ℝ) : ℝ :=
  P.diffusivity * (∑ e, ∫ x in (0 : ℝ)..P.length e, deriv (u e) x ^ 2) +
    ∑ v, P.strength v * U v ^ 2

noncomputable def SpectralNetwork.squareMass [Fintype E]
    (P : SpectralNetwork V E) (u : E → ℝ → ℝ) : ℝ :=
  ∑ e, ∫ x in (0 : ℝ)..P.length e, u e x ^ 2

def SpectralNetwork.rayleighValues [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) : Set ℝ :=
  {r | ∃ U : V → ℝ, ∃ u : E → ℝ → ℝ, GraphEnergy P.geometry U u ∧
    0 < P.squareMass u ∧ r = P.quadraticForm U u / P.squareMass u}

noncomputable def SpectralNetwork.principalValue [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) : ℝ := sInf P.rayleighValues

theorem SpectralNetwork.totalLength_pos [Fintype E] [Nonempty E]
    (P : SpectralNetwork V E) : 0 < P.totalLength :=
  Finset.sum_pos (fun e _ => P.length_pos e) Finset.univ_nonempty

theorem SpectralNetwork.totalStrength_pos [Fintype V] [Nonempty V]
    (P : SpectralNetwork V E) : 0 < P.totalStrength :=
  Finset.sum_pos (fun v _ => P.strength_pos v) Finset.univ_nonempty

theorem SpectralNetwork.quadraticForm_nonneg [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) (U : V → ℝ) (u : E → ℝ → ℝ) :
    0 ≤ P.quadraticForm U u := by
  refine add_nonneg (mul_nonneg P.diffusivity_pos.le ?_) ?_
  · exact Finset.sum_nonneg fun e _ => intervalIntegral.integral_nonneg
      (P.length_pos e).le (fun x _ => sq_nonneg (deriv (u e) x))
  · exact Finset.sum_nonneg fun v _ => mul_nonneg (P.strength_pos v).le (sq_nonneg _)

theorem SpectralNetwork.squareMass_one [Fintype E] (P : SpectralNetwork V E) :
    P.squareMass (fun _ _ => 1) = P.totalLength := by
  simp [squareMass, totalLength]

theorem SpectralNetwork.quadraticForm_one [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) :
    P.quadraticForm (fun _ => 1) (fun _ _ => 1) = P.totalStrength := by
  simp [quadraticForm, totalStrength]

theorem SpectralNetwork.rayleighValues_nonempty [Fintype V] [Fintype E] [Nonempty E]
    (P : SpectralNetwork V E) : P.rayleighValues.Nonempty := by
  refine ⟨P.quadraticForm (fun _ => 1) (fun _ _ => 1) / P.squareMass (fun _ _ => 1),
    (fun _ => 1), (fun _ _ => 1), GraphEnergy.const P.geometry 1, ?_, rfl⟩
  rw [P.squareMass_one]
  exact P.totalLength_pos

theorem SpectralNetwork.rayleighValues_bddBelow [Fintype V] [Fintype E]
    (P : SpectralNetwork V E) : BddBelow P.rayleighValues := by
  refine ⟨0, ?_⟩
  rintro r ⟨U, u, _, hm, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg U u) hm.le

theorem SpectralNetwork.principalValue_nonneg [Fintype V] [Fintype E] [Nonempty E]
    (P : SpectralNetwork V E) : 0 ≤ P.principalValue := by
  apply le_csInf P.rayleighValues_nonempty
  rintro r ⟨U, u, _, hm, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg U u) hm.le

theorem SpectralNetwork.principalValue_le_constant [Fintype V] [Fintype E] [Nonempty E]
    (P : SpectralNetwork V E) : P.principalValue ≤ P.totalStrength / P.totalLength := by
  apply csInf_le P.rayleighValues_bddBelow
  refine ⟨(fun _ => 1), (fun _ _ => 1), GraphEnergy.const P.geometry 1, ?_, ?_⟩
  · rw [P.squareMass_one]
    exact P.totalLength_pos
  · rw [P.squareMass_one, P.quadraticForm_one]

end TimeTraps.Spectral
