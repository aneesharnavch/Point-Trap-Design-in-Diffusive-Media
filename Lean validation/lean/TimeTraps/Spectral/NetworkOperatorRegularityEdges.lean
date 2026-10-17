module

public import TimeTraps.Spectral.NetworkOperatorRegularityTests

@[expose] public section

/-! Interior compact tests derive the distributional second derivative
on each whole physical edge. Sobolev representation then supplies an
actual AC/L2 slope for arbitrary edge L2 forcing, with no C2 hypothesis. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped ContDiff

variable {V E : Type*} [Fintype V] [Fintype E]
variable {P : SpectralNetwork V E} {f : GraphL2Product P.geometry}
variable {U : V → ℝ} {u : E → ℝ → ℝ}

theorem NetworkL2WeakEquation.edge_test (h : NetworkL2WeakEquation P f U u)
    (e : E) {φ : ℝ → ℝ} (hc : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo 0 (P.length e)) :
    P.diffusivity * (∫ x in (0 : ℝ)..P.length e, deriv (u e) x * deriv φ x) =
      ∫ x in (0 : ℝ)..P.length e, (f e) x * φ x := by
  classical
  have hsame : P.operatorEdgeTest e φ e = φ := by
    funext x
    simp only [SpectralNetwork.operatorEdgeTest, ↓reduceIte]
  have hother (d : E) (hd : d ≠ e) : P.operatorEdgeTest e φ d = fun _ => 0 := by
    funext x
    simp only [SpectralNetwork.operatorEdgeTest, hd, ↓reduceIte]
  have he := h.weak_form (fun _ => 0) (P.operatorEdgeTest e φ) (P.operatorEdgeTest_energy e hc hs)
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at he
  have hl : (∑ d, ∫ x in (0 : ℝ)..P.length d,
      P.diffusivity * deriv (u d) x * deriv (P.operatorEdgeTest e φ d) x) =
      P.diffusivity * (∫ x in (0 : ℝ)..P.length e, deriv (u e) x * deriv φ x) := by
    rw [Finset.sum_eq_single e]
    · simp only [hsame, mul_assoc,
        intervalIntegral.integral_const_mul]
    · intro d _ hd
      simp only [hother d hd, deriv_const, mul_zero,
        intervalIntegral.integral_zero]
    · simp
  have hr : (∑ d, ∫ x in (0 : ℝ)..P.length d, (f d) x * P.operatorEdgeTest e φ d x) =
      ∫ x in (0 : ℝ)..P.length e, (f e) x * φ x := by
    rw [Finset.sum_eq_single e]
    · simp only [SpectralNetwork.operatorEdgeTest, ↓reduceIte]
    · intro d _ hd
      simp only [SpectralNetwork.operatorEdgeTest, hd, ↓reduceIte, mul_zero,
        intervalIntegral.integral_zero]
    · simp
  rwa [hl, hr] at he

theorem NetworkL2WeakEquation.edge_weak_second (h : NetworkL2WeakEquation P f U u) (e : E) :
    IntervalWeakDerivative (deriv (u e)) (fun x => -(f e) x / P.diffusivity) 0 (P.length e) := by
  intro φ hc _ hs
  have he := h.edge_test e hc hs
  rw [intervalSobolev_test_integral (P.length_pos e).le (tsupport_deriv_subset.trans hs),
    intervalSobolev_test_integral (P.length_pos e).le hs] at he
  have hi : (∫ x, (-(f e) x / P.diffusivity) * φ x) =
      -(∫ x, (f e) x * φ x) / P.diffusivity := by
    calc
      _ = ∫ x, -((f e) x * φ x) / P.diffusivity := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_div, integral_neg]
  rw [hi, neg_div, neg_neg]
  exact (eq_div_iff P.diffusivity_pos.ne').mpr (by simpa only [mul_comm] using he)

theorem NetworkL2WeakEquation.edge_regularity (h : NetworkL2WeakEquation P f U u) (e : E) :
    ∃ j : ℝ → ℝ, IntervalSlopeRegularity (u e) j
      (fun x => -(f e) x / P.diffusivity) 0 (P.length e) := by
  have hf : MemLp (fun x => -(f e) x / P.diffusivity) 2
      (volume.restrict (Ioo 0 (P.length e))) := by
    have hfe : MemLp (f e) 2 (volume.restrict (Ioo 0 (P.length e))) := Lp.memLp (f e)
    simpa only [neg_mul, neg_div, div_eq_mul_inv, mul_comm, mul_neg] using
      hfe.const_mul (-P.diffusivity⁻¹)
  have hd : MemLp (deriv (u e)) 2 (volume.restrict (Ioo 0 (P.length e))) := by
    have hue : IntervalEnergy (u e) 0 (P.length e) := h.energy.edge_energy e
    apply hue.derivative_memLp.mono_measure
    rw [uIoc_of_le (P.length_pos e).le]
    exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
  obtain ⟨j, hj, huj, hgj⟩ := (h.edge_weak_second e).energy_representative (P.length_pos e)
    (show IntegrableOn (deriv (u e)) (Ioo 0 (P.length e)) volume from
      hd.integrable (by norm_num)).locallyIntegrableOn hf
  exact ⟨j, h.energy.edge_energy e, hj, huj, hgj.symm⟩

end TimeTraps.Spectral
