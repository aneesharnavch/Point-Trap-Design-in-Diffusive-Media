module

public import TimeTraps.Graph.MetricState
public import TimeTraps.Analysis.IntervalSobolevSpacePairing
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Finite Hilbert products of the actual edge H1 and L2 spaces. The
product norm is the square-sum norm on `PiLp 2`. Only the finite edge
index and the given edge lengths enter; no incidence or nonemptiness
condition is imposed, and no vertex trace matching is imposed yet. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph IntervalSobolevSpace
open scoped InnerProductSpace

variable {V E : Type*}

abbrev GraphSobolevProduct (G : MetricGraph V E) :=
  PiLp 2 (fun e : E => IntervalSobolevSpace 0 (G.length e))

abbrev GraphL2Product (G : MetricGraph V E) :=
  PiLp 2 (fun e : E => IntervalSobolevL2 0 (G.length e))

noncomputable def graphSobolevComponentL (G : MetricGraph V E) (e : E) :
    GraphSobolevProduct G →L[ℝ] IntervalSobolevSpace 0 (G.length e) :=
  PiLp.proj 2 (fun d : E => IntervalSobolevSpace 0 (G.length d)) e

noncomputable def graphL2ComponentL (G : MetricGraph V E) (e : E) :
    GraphL2Product G →L[ℝ] IntervalSobolevL2 0 (G.length e) :=
  PiLp.proj 2 (fun d : E => IntervalSobolevL2 0 (G.length d)) e

theorem graphSobolevComponentL_apply (G : MetricGraph V E) (e : E)
    (u : GraphSobolevProduct G) : graphSobolevComponentL G e u = u e := rfl

theorem graphL2ComponentL_apply (G : MetricGraph V E) (e : E)
    (f : GraphL2Product G) : graphL2ComponentL G e f = f e := rfl

noncomputable def graphSobolevStateL (G : MetricGraph V E) :
    GraphSobolevProduct G →L[ℝ] GraphL2Product G :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun e : E => IntervalSobolevL2 0 (G.length e))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun e =>
        (IntervalSobolevSpace.stateL 0 (G.length e)).comp (graphSobolevComponentL G e))

theorem graphSobolevStateL_apply (G : MetricGraph V E)
    (u : GraphSobolevProduct G) (e : E) : (graphSobolevStateL G u) e = (u e).state := rfl

theorem graphSobolevStateL_injective (G : MetricGraph V E) :
    Function.Injective (graphSobolevStateL G) := by
  intro u v h
  apply PiLp.ext
  intro e
  apply IntervalSobolevSpace.ext_state
  exact congrArg (fun f : GraphL2Product G => f e) h

theorem graphSobolevProduct_norm_sq [Fintype E] (G : MetricGraph V E) (u : GraphSobolevProduct G) :
    ‖u‖ ^ 2 = ∑ e, ‖u e‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ u

theorem graphL2Product_norm_sq [Fintype E] (G : MetricGraph V E) (f : GraphL2Product G) :
    ‖f‖ ^ 2 = ∑ e, ‖f e‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ f

theorem graphSobolevProduct_inner [Fintype E] (G : MetricGraph V E) (u v : GraphSobolevProduct G) :
    ⟪u, v⟫_ℝ = ∑ e, ⟪u e, v e⟫_ℝ := PiLp.inner_apply u v

theorem graphL2Product_inner [Fintype E] (G : MetricGraph V E) (f g : GraphL2Product G) :
    ⟪f, g⟫_ℝ = ∑ e, ⟪f e, g e⟫_ℝ := PiLp.inner_apply f g

end TimeTraps.Analysis
