module

public import TimeTraps.Analysis.GraphContactCoercivity
public import TimeTraps.Analysis.IntervalPointFormHilbert

@[expose] public section

/-! Multiplication by the original continuous edge conductance is a
bounded linear map on the actual edge L2 space. The coefficient is not
replaced by a constant or assumed to be smooth. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*}

noncomputable def graphContactOperatorCoefficient (G : MetricGraph V E) (e : E) :
    C(Icc (0 : ℝ) (G.length e), ℝ) :=
  ⟨fun x => G.conductance e x, continuousOn_iff_continuous_domRestrict.mp (G.conductance_continuous e)⟩

theorem graphContactOperatorCoefficient_bound (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Icc 0 (G.length e)) :
    ‖G.conductance e x‖ ≤ ‖graphContactOperatorCoefficient G e‖ :=
  (graphContactOperatorCoefficient G e).norm_coe_le_norm ⟨x, hx⟩

theorem graphContactOperatorMultiply_memLp (G : MetricGraph V E) (e : E)
    (f : IntervalSobolevL2 0 (G.length e)) :
    MemLp (fun x => G.conductance e x * f x) 2 (volume.restrict (Ioo 0 (G.length e))) := by
  apply (Lp.memLp f).of_le_mul (c := ‖graphContactOperatorCoefficient G e‖)
    (((G.conductance_continuous e).mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo |>.mul
      (Lp.aestronglyMeasurable f))
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (graphContactOperatorCoefficient_bound G e (Ioo_subset_Icc_self hx))
    (norm_nonneg _)

noncomputable def graphContactOperatorMultiply (G : MetricGraph V E) (e : E)
    (f : IntervalSobolevL2 0 (G.length e)) : IntervalSobolevL2 0 (G.length e) :=
  (graphContactOperatorMultiply_memLp G e f).toLp (fun x => G.conductance e x * f x)

theorem graphContactOperatorMultiply_coe (G : MetricGraph V E) (e : E)
    (f : IntervalSobolevL2 0 (G.length e)) :
    graphContactOperatorMultiply G e f =ᵐ[volume.restrict (Ioo 0 (G.length e))]
      (fun x => G.conductance e x * f x) :=
  (graphContactOperatorMultiply_memLp G e f).coeFn_toLp

noncomputable def graphContactOperatorMultiplyLinear (G : MetricGraph V E) (e : E) :
    IntervalSobolevL2 0 (G.length e) →ₗ[ℝ] IntervalSobolevL2 0 (G.length e) where
  toFun := graphContactOperatorMultiply G e
  map_add' f g := by
    apply Lp.ext
    filter_upwards [graphContactOperatorMultiply_coe G e (f + g), Lp.coeFn_add f g,
      graphContactOperatorMultiply_coe G e f, graphContactOperatorMultiply_coe G e g,
      Lp.coeFn_add (graphContactOperatorMultiply G e f) (graphContactOperatorMultiply G e g)]
      with x hsum hfg hf hg hout
    simp only [hsum, hfg, hout, Pi.add_apply, hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [graphContactOperatorMultiply_coe G e (c • f), Lp.coeFn_smul c f,
      graphContactOperatorMultiply_coe G e f, Lp.coeFn_smul c (graphContactOperatorMultiply G e f)]
      with x hprod hcf hf hout
    simp only [hprod, hcf, hout, hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem graphContactOperatorMultiply_norm_le (G : MetricGraph V E) (e : E)
    (f : IntervalSobolevL2 0 (G.length e)) :
    ‖graphContactOperatorMultiply G e f‖ ≤ ‖graphContactOperatorCoefficient G e‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [graphContactOperatorMultiply_coe G e f,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x he hx
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right (graphContactOperatorCoefficient_bound G e (Ioo_subset_Icc_self hx))
    (norm_nonneg _)

noncomputable def graphContactOperatorMultiplyL (G : MetricGraph V E) (e : E) :
    IntervalSobolevL2 0 (G.length e) →L[ℝ] IntervalSobolevL2 0 (G.length e) :=
  (graphContactOperatorMultiplyLinear G e).mkContinuous ‖graphContactOperatorCoefficient G e‖
    (graphContactOperatorMultiply_norm_le G e)

theorem graphContactOperatorMultiplyL_coe (G : MetricGraph V E) (e : E)
    (f : IntervalSobolevL2 0 (G.length e)) :
    graphContactOperatorMultiplyL G e f =ᵐ[volume.restrict (Ioo 0 (G.length e))]
      (fun x => G.conductance e x * f x) := graphContactOperatorMultiply_coe G e f

end TimeTraps.Analysis
