module

public import TimeTraps.Probability.DyadicStieltjesRightIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! Actual integration by parts for two continuous increasing functions.
Both measure integrals are integrable on compact time intervals. The
proof takes the two already proved dyadic Stieltjes limits in the exact
finite product identity and allows arbitrary initial values. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal Topology

theorem continuousNNReal_stieltjes_integrable (K : StieltjesFunction ℝ)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) (T : ℝ≥0) :
    IntegrableOn (fun r : ℝ => g r.toNNReal) (Ioc (0 : ℝ) T.val) K.measure :=
  (hg.comp continuous_real_toNNReal).integrableOn_Ioc

theorem stieltjes_product_integrable (K Q : StieltjesFunction ℝ)
    (hK : Continuous K) (hQ : Continuous Q) (c : ℝ) (T : ℝ≥0) :
    IntegrableOn (fun r => c - K r) (Ioc (0 : ℝ) T.val) Q.measure ∧
      IntegrableOn (fun r => Q r) (Ioc (0 : ℝ) T.val) K.measure :=
  ⟨(continuous_const.sub hK).integrableOn_Ioc, hQ.integrableOn_Ioc⟩

theorem stieltjes_product (K Q : StieltjesFunction ℝ)
    (hK : Continuous K) (hQ : Continuous Q) (c : ℝ) (T : ℝ≥0) :
    (c - K T.val) * Q T.val - (c - K 0) * Q 0 =
      (∫ r in Ioc (0 : ℝ) T.val, c - K r ∂Q.measure) -
        ∫ r in Ioc (0 : ℝ) T.val, Q r ∂K.measure := by
  let H : ℝ≥0 → ℝ := fun t => c - K t.val
  let g : ℝ≥0 → ℝ := fun t => Q t.val
  have hh : Continuous H := continuous_const.sub (hK.comp continuous_subtype_val)
  have hg : Continuous g := hQ.comp continuous_subtype_val
  have hleft := dyadicStieltjesSum_tendsto Q H hh T
  have hright := dyadicStieltjesRightSum_tendsto K g hg T
  have he (n : ℕ) : dyadicStieltjesSum Q H T n - dyadicStieltjesRightSum K g T n =
      (c - K T.val) * Q T.val - (c - K 0) * Q 0 := by
    have hi := dyadicStieltjes_product_identity K g c T n
    have hs : dyadicStieltjesSum Q H T n =
        ∑ i : Fin (2 ^ n), (c - K (brownianDyadicGrid T n i.castSucc).val) *
          (g (brownianDyadicGrid T n i.succ) - g (brownianDyadicGrid T n i.castSucc)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [hs]
    exact hi.symm
  have hlim : Tendsto (fun _ : ℕ => (c - K T.val) * Q T.val - (c - K 0) * Q 0) atTop
      (𝓝 ((∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal ∂Q.measure) -
        ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂K.measure)) := by
    simpa only [he] using hleft.sub hright
  have hI : (∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal ∂Q.measure) =
      ∫ r in Ioc (0 : ℝ) T.val, c - K r ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change c - K r.toNNReal.val = c - K r
    rw [Real.toNNReal_of_nonneg hr.1.le]
    rfl
  have hJ : (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂K.measure) =
      ∫ r in Ioc (0 : ℝ) T.val, Q r ∂K.measure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change Q r.toNNReal.val = Q r
    rw [Real.toNNReal_of_nonneg hr.1.le]
    rfl
  rw [hI, hJ] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end TimeTraps.Probability
