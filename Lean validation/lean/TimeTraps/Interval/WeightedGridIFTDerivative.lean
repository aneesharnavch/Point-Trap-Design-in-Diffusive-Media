module

public import TimeTraps.Interval.WeightedGridIFTResidual

@[expose] public section

/-! Identification of the actual Fréchet derivative of the smooth centroid
residual at the equal grid. The grid block is the proved invertible
Dirichlet Jacobian; the parameter derivative is the signed h moment. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped ContDiff

variable {n : ℕ}

theorem gridIFT_nodes_add (q r : Fin n → ℝ) (t : ℝ) (v : Fin (n + 2)) :
    cdfNode (fun i => q i + t * r i) v = cdfNode q v + t * nodalStrength r v := by
  refine Fin.cases ?_ (fun k => ?_) v
  · simp only [cdfNode_first, nodalStrength_first, mul_zero, add_zero]
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change cdfNode _ (Fin.last (n + 1)) = cdfNode _ (Fin.last (n + 1)) + t * nodalStrength _ (Fin.last (n + 1))
      simp only [cdfNode_last, nodalStrength_last, mul_zero, add_zero]
    · change cdfNode _ (trapNode i) = cdfNode _ (trapNode i) + t * nodalStrength _ (trapNode i)
      simp only [trapNode, cdfNode_site]
      rw [show nodalStrength r i.castSucc.succ = r i from nodalStrength_trap r i]

theorem gridIFTLeft_add (q r : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    gridIFTLeft (fun j => q j + t * r j) i = gridIFTLeft q i + t * (nodalStrength r i.castSucc.castSucc + r i) / 2 := by
  simp only [gridIFTLeft, gridIFT_nodes_add]
  ring

theorem gridIFTRight_add (q r : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    gridIFTRight (fun j => q j + t * r j) i = gridIFTRight q i + t * (r i + nodalStrength r i.succ.succ) / 2 := by
  simp only [gridIFTRight, gridIFT_nodes_add]
  ring

theorem gridIFTResidual_grid_curve_derivative (h : ℝ → ℝ) (Ω : ℝ) (r : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => gridIFTResidual h Ω (0, fun j => gridIFTBaseline n j + t * r j) i)
      (weightedGridUniformJacobian n Ω r i) 0 := by
  let q := gridIFTBaseline n
  let a := gridIFTLeft q i
  let b := gridIFTRight q i
  let da := (nodalStrength r i.castSucc.castSucc + r i) / 2
  let db := (r i + nodalStrength r i.succ.succ) / 2
  have hq : HasDerivAt (fun t => q i + t * r i) (r i) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const (r i)).const_add (q i) using 1
    simp only [one_mul]
  have ha : HasDerivAt (fun t => a + t * da) da 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const da).const_add a using 1
    simp only [one_mul]
  have hb : HasDerivAt (fun t => b + t * db) db 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const db).const_add b using 1
    simp only [one_mul]
  have hd := ((hq.mul (hb.sub ha)).sub (((hb.pow 2).sub (ha.pow 2)).div_const 2)).const_mul Ω
  have hf : (fun t => gridIFTResidual h Ω (0, fun j => gridIFTBaseline n j + t * r j) i) =
      fun t => Ω * ((q i + t * r i) * ((b + t * db) - (a + t * da)) -
        ((b + t * db) ^ 2 - (a + t * da) ^ 2) / 2) := by
    funext t
    simp only [gridIFTResidual, zero_mul, add_zero, gridIFTLeft_add, gridIFTRight_add]
    dsimp only [q, a, b, da, db]
    ring
  rw [hf]
  convert! hd using 1
  change (Ω / (4 * ((n : ℝ) + 1))) * TimeTraps.Analysis.discreteSecondDifference (nodalStrength r) i = _
  simp only [TimeTraps.Analysis.discreteSecondDifference, Fin.castSucc_succ,
    show nodalStrength r i.castSucc.succ = r i from nodalStrength_trap r i]
  dsimp only [q, a, b, da, db]
  simp only [gridIFTLeft, gridIFTRight, gridIFTBaseline_nodes, gridIFTBaseline, StrictPartition.uniform,
    Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Pi.sub_apply, zero_mul, add_zero]
  ring_nf
  field_simp
  ring

theorem gridIFTResidual_fderiv_grid (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) :
    (fderiv ℝ (gridIFTResidual h Ω) (0, gridIFTBaseline n)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) =
      (weightedGridUniformJacobian n Ω).toContinuousLinearMap := by
  have hf := ((gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).differentiableAt
    (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt
  ext r i
  have hp : HasDerivAt (fun t : ℝ => ((0 : ℝ), fun j => gridIFTBaseline n j + t * r j)) (0, r) 0 := by
    have hq := ((hasDerivAt_id (0 : ℝ)).smul_const r).const_add (gridIFTBaseline n)
    convert! (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hq using 1
    simp only [one_smul]
  have hc := hf.comp_hasDerivAt_of_eq 0 hp (by simp only [zero_mul, add_zero])
  have hi := hasDerivAt_pi.mp hc i
  exact hi.unique (gridIFTResidual_grid_curve_derivative h Ω r i)

noncomputable def gridIFTForcing (h : ℝ → ℝ) (i : Fin n) : ℝ :=
  ∫ z in gridIFTLeft (gridIFTBaseline n) i..gridIFTRight (gridIFTBaseline n) i,
    h z * (gridIFTBaseline n i - z)

theorem gridIFTResidual_fderiv_parameter (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) :
    (fderiv ℝ (gridIFTResidual h Ω) (0, gridIFTBaseline n)) (1, 0) = Ω • gridIFTForcing h := by
  have hf := ((gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).differentiableAt
    (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hp : HasDerivAt (fun t : ℝ => (t, gridIFTBaseline n)) (1, 0) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (gridIFTBaseline n)) using 1
  have hc := hf.comp_hasDerivAt 0 hp
  funext i
  exact (hasDerivAt_pi.mp hc i).unique (gridIFTResidual_epsilon_derivative h hh.continuousOn Ω 0
    (gridIFTBaseline n) i (Ioo_subset_Icc_self (gridIFTBaseline_midpoints i).1)
      (Ioo_subset_Icc_self (gridIFTBaseline_midpoints i).2))

theorem gridIFTResidual_grid_invertible (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ((fderiv ℝ (gridIFTResidual h Ω) (0, gridIFTBaseline n)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))).IsInvertible := by
  rw [gridIFTResidual_fderiv_grid h hh Ω]
  exact ⟨(weightedGridUniformJacobianEquiv n Ω hΩ).toContinuousLinearEquiv, rfl⟩

end TimeTraps.Interval
