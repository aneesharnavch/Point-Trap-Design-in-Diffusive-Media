module

public import TimeTraps.Spectral.NetworkOperatorSelfAdjointPhysical
public import TimeTraps.Analysis.IntervalPointRegularityData

@[expose] public section

/-! Actual graph H1 tests supported inside one edge and actual affine
interpolants of arbitrary nodal data. Both ends of a loop obey the same
nodal value; no edge ordering or distinct-endpoint premise is used. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Graph
open scoped ContDiff

variable {V E : Type*}

noncomputable def SpectralNetwork.operatorEdgeTest (_P : SpectralNetwork V E)
    (e : E) (φ : ℝ → ℝ) (d : E) (x : ℝ) : ℝ := by
  classical
  exact if d = e then φ x else 0

theorem SpectralNetwork.operatorEdgeTest_energy (P : SpectralNetwork V E)
    (e : E) {φ : ℝ → ℝ} (hc : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo 0 (P.length e)) :
    GraphEnergy P.geometry (fun _ => 0) (P.operatorEdgeTest e φ) := by
  classical
  have hz (x : ℝ) (hx : x ∉ Ioo 0 (P.length e)) : φ x = 0 := by
    by_contra hn
    exact hx (hs (subset_closure hn))
  refine ⟨?_, ?_, ?_⟩
  · intro d
    change IntervalEnergy (fun x => if d = e then φ x else 0) 0 (P.length d)
    by_cases hd : d = e
    · subst d
      simpa only [↓reduceIte] using
        intervalEnergy_of_continuous_derivative (P.length_pos e).le
          hc.continuous.continuousOn (hc.continuous_deriv (by simp)).continuousOn
          (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
    · simpa only [hd, ↓reduceIte] using IntervalEnergy.const 0 0 (P.length d)
  · intro d
    change (if d = e then φ 0 else 0) = 0
    by_cases hd : d = e
    · subst d
      simp only [↓reduceIte, hz 0 (by simp)]
    · simp only [hd, ↓reduceIte]
  · intro d
    change (if d = e then φ (P.length d) else 0) = 0
    by_cases hd : d = e
    · subst d
      simp only [↓reduceIte, hz (P.length e) (by simp)]
    · simp only [hd, ↓reduceIte]

noncomputable def SpectralNetwork.operatorNodeTest (P : SpectralNetwork V E)
    (W : V → ℝ) (e : E) (x : ℝ) : ℝ :=
  W (P.tail e) + (W (P.head e) - W (P.tail e)) / P.length e * x

theorem SpectralNetwork.operatorNodeTest_energy (P : SpectralNetwork V E) (W : V → ℝ) :
    GraphEnergy P.geometry W (P.operatorNodeTest W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    change IntervalEnergy
      (fun x => W (P.tail e) + (W (P.head e) - W (P.tail e)) / P.length e * x) 0 (P.length e)
    apply intervalEnergy_of_continuous_derivative (P.length_pos e).le
      (g := fun _ => (W (P.head e) - W (P.tail e)) / P.length e)
    · fun_prop
    · exact continuousOn_const
    · intro x _
      simpa only [mul_one, id_eq] using
        ((hasDerivAt_id x).const_mul ((W (P.head e) - W (P.tail e)) / P.length e)).const_add
          (W (P.tail e))
  · intro e
    change W (P.tail e) + (W (P.head e) - W (P.tail e)) / P.length e * 0 = W (P.tail e)
    simp only [mul_zero, add_zero]
  · intro e
    change W (P.tail e) + (W (P.head e) - W (P.tail e)) / P.length e * P.length e = W (P.head e)
    rw [div_mul_cancel₀ _ (P.length_pos e).ne']
    ring

end TimeTraps.Spectral
