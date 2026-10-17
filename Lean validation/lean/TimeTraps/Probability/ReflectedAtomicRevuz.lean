module

public import TimeTraps.Probability.ReflectedAtomicRevuzFubini
public import TimeTraps.Probability.ReflectedGaussianReversible
public import TimeTraps.Analysis.ReflectedAtomicRevuzAverage

@[expose] public section

/-! Fixed-interior-atom short-time test normalization for the actual
constructed occupation measure. The reference measure dx gives h(a)g(a);
the normalized uniform reference dx/L gives h(a)g(a)/L. The expectations
and exchanges of integrals are derived, and no PCAF cocycle is claimed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedAtomicRevuzMeanTest (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a : ℝ)
    (h g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) (x : ℝ) : ℝ :=
  reflectedFellerExtension L hL h x *
    ∫ ω, reflectedAtomicRevuzContact L hL D hD x a g T ω ∂brownianDyadicMeasure

theorem reflectedAtomicRevuzMeanTest_integrable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (h g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    IntegrableOn (reflectedAtomicRevuzMeanTest L hL D hD a h g T) (Ioo (0 : ℝ) L) volume := by
  apply ((reflectedAtomicRevuzKernel_spatial_integrable L hL D hD
    ⟨a, Ioo_subset_Icc_self ha⟩ h T).const_mul (g ⟨a, Ioo_subset_Icc_self ha⟩)).congr
  filter_upwards [] with x
  unfold reflectedAtomicRevuzMeanTest
  rw [reflectedAtomicRevuzContact_mean L hL D hD x a ha g T]
  ring

theorem reflectedAtomicRevuzMeanTest_spatial_identity (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (h g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    (∫ x in Ioo (0 : ℝ) L, reflectedAtomicRevuzMeanTest L hL D hD a h g T x) =
      g ⟨a, Ioo_subset_Icc_self ha⟩ *
        ∫ r in (0 : ℝ)..T.val, reflectedFellerTimeOperator L hL D r h ⟨a, Ioo_subset_Icc_self ha⟩ := by
  calc
    _ = ∫ x in Ioo (0 : ℝ) L, g ⟨a, Ioo_subset_Icc_self ha⟩ *
        (reflectedFellerExtension L hL h x *
          ∫ r in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * r).toNNReal a) := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold reflectedAtomicRevuzMeanTest
      rw [reflectedAtomicRevuzContact_mean L hL D hD x a ha g T]
      ring
    _ = _ := by
      rw [integral_const_mul, reflectedAtomicRevuzKernel_spatial_identity L hL D hD
        ⟨a, Ioo_subset_Icc_self ha⟩ h T]

theorem reflectedAtomicRevuzMeanTest_uniform (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a : ℝ) (h g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    (∫ x, reflectedAtomicRevuzMeanTest L hL D hD a h g T x ∂reflectedUniformLaw L hL) =
      (1 / L) * ∫ x in Ioo (0 : ℝ) L, reflectedAtomicRevuzMeanTest L hL D hD a h g T x := by
  rw [reflectedUniformLaw_eq_open, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hL.le, smul_eq_mul, one_div]

theorem reflectedAtomicRevuz_limit_volume (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (h g : C(Icc (0 : ℝ) L, ℝ)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x in Ioo (0 : ℝ) L,
      reflectedAtomicRevuzMeanTest L hL D hD a h g t.toNNReal x) (𝓝[>] 0)
        (𝓝 (h ⟨a, Ioo_subset_Icc_self ha⟩ * g ⟨a, Ioo_subset_Icc_self ha⟩)) := by
  let a₀ : Icc (0 : ℝ) L := ⟨a, Ioo_subset_Icc_self ha⟩
  let f : ℝ → ℝ := fun r => reflectedFellerTimeOperator L hL D r h a₀
  have hf : Continuous f := (continuous_eval_const a₀).comp
    (reflectedFellerTimeOperator_continuous L hL D h)
  have hzero : f 0 = h a₀ := by
    simp only [f, reflectedFellerTimeOperator, mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero]
  have hlim := (reflectedAtomicRevuz_continuous_average hf).const_mul (g a₀)
  rw [hzero, mul_comm (g a₀) (h a₀)] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hT : t.toNNReal.val = t := Real.coe_toNNReal t (le_of_lt ht)
  have htime : (∫ r in (0 : ℝ)..t.toNNReal.val, f r) = ∫ r in (0 : ℝ)..t, f r :=
    congrArg (fun q : ℝ => ∫ r in (0 : ℝ)..q, f r) hT
  have hs := reflectedAtomicRevuzMeanTest_spatial_identity L hL D hD a ha h g t.toNNReal
  change (∫ x in Ioo (0 : ℝ) L, reflectedAtomicRevuzMeanTest L hL D hD a h g t.toNNReal x) =
    g a₀ * ∫ r in (0 : ℝ)..t.toNNReal.val, f r at hs
  calc
    g a₀ * (t⁻¹ * ∫ r in (0 : ℝ)..t, f r) =
        t⁻¹ * (g a₀ * ∫ r in (0 : ℝ)..t, f r) := by ring
    _ = t⁻¹ * (g a₀ * ∫ r in (0 : ℝ)..t.toNNReal.val, f r) :=
      congrArg (fun z : ℝ => t⁻¹ * (g a₀ * z)) htime.symm
    _ = _ := congrArg (fun z : ℝ => t⁻¹ * z) hs.symm

theorem reflectedAtomicRevuz_limit_uniform (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (h g : C(Icc (0 : ℝ) L, ℝ)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x,
      reflectedAtomicRevuzMeanTest L hL D hD a h g t.toNNReal x ∂reflectedUniformLaw L hL)
      (𝓝[>] 0) (𝓝 ((h ⟨a, Ioo_subset_Icc_self ha⟩ * g ⟨a, Ioo_subset_Icc_self ha⟩) / L)) := by
  have he : (fun t : ℝ => t⁻¹ * ∫ x,
      reflectedAtomicRevuzMeanTest L hL D hD a h g t.toNNReal x ∂reflectedUniformLaw L hL) =
      (fun t : ℝ => (1 / L) * (t⁻¹ * ∫ x in Ioo (0 : ℝ) L,
        reflectedAtomicRevuzMeanTest L hL D hD a h g t.toNNReal x)) := by
    funext t
    rw [reflectedAtomicRevuzMeanTest_uniform]
    ring
  rw [he]
  simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using
    (reflectedAtomicRevuz_limit_volume L hL D hD a ha h g).const_mul (1 / L)

end TimeTraps.Probability

end
