module

public import TimeTraps.Probability.ReflectedNeumannProblem
public import TimeTraps.Probability.ReflectedUniformL2Normalization
public import TimeTraps.Probability.ReflectedCosinePhysicalGenerator
public import TimeTraps.Probability.ReflectedFoldCosineEvolution

@[expose] public section

/-! Actual normalized cosine representatives in the empty-contact Neumann
operator graph. Their AC states and slopes are constructed from the
classical derivatives. Finite graph sums follow from linearity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

def reflectedNormalizedCosine (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  reflectedCosineScale n * Real.cos (((n : ℝ) * Real.pi / L) * x)

def reflectedNormalizedCosineSlope (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  reflectedCosineScale n * (-Real.sin (((n : ℝ) * Real.pi / L) * x) * ((n : ℝ) * Real.pi / L))

theorem reflectedNormalizedCosine_derivative (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (reflectedNormalizedCosine L n) (reflectedNormalizedCosineSlope L n x) x :=
  (reflectedCosine_derivative L n x).const_mul (reflectedCosineScale n)

theorem reflectedNormalizedCosineSlope_derivative (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (reflectedNormalizedCosineSlope L n)
      (-((n : ℝ) * Real.pi / L) ^ 2 * reflectedNormalizedCosine L n x) x := by
  have hd := (((((hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)).sin).neg.mul_const
    ((n : ℝ) * Real.pi / L)).const_mul (reflectedCosineScale n))
  simp only [id_eq, Pi.neg_apply, mul_one] at hd
  exact hd.congr_deriv (by unfold reflectedNormalizedCosine; ring)

theorem reflectedNormalizedCosine_regularity (L : ℝ) (hL : 0 < L) (n : ℕ) :
    IntervalSlopeRegularity (reflectedNormalizedCosine L n) (reflectedNormalizedCosineSlope L n)
      (fun x => -((n : ℝ) * Real.pi / L) ^ 2 * reflectedNormalizedCosine L n x) 0 L := by
  have hu : Continuous (reflectedNormalizedCosine L n) := by
    unfold reflectedNormalizedCosine
    fun_prop
  have hj : Continuous (reflectedNormalizedCosineSlope L n) := by
    unfold reflectedNormalizedCosineSlope
    fun_prop
  refine ⟨intervalEnergy_of_continuous_derivative hL.le hu.continuousOn hj.continuousOn
      (fun x _ => reflectedNormalizedCosine_derivative L n x),
    intervalEnergy_of_continuous_derivative hL.le hj.continuousOn
      ((continuous_const.mul hu).continuousOn)
      (fun x _ => reflectedNormalizedCosineSlope_derivative L n x), ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun x => (reflectedNormalizedCosine_derivative L n x).deriv)
  · exact Filter.Eventually.of_forall (fun x => (reflectedNormalizedCosineSlope_derivative L n x).deriv)

theorem reflectedNormalizedCosine_neumann (L : ℝ) (hL : 0 < L) (n : ℕ) :
    reflectedNormalizedCosineSlope L n 0 = 0 ∧ reflectedNormalizedCosineSlope L n L = 0 := by
  simp [reflectedNormalizedCosineSlope, div_mul_cancel₀ _ hL.ne', Real.sin_nat_mul_pi]

theorem reflectedUniformL2Equiv_cosine_coe (L : ℝ) (hL : 0 < L) (n : ℕ) :
    reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n) =ᵐ[volume.restrict (Ioo 0 L)]
      reflectedNormalizedCosine L n := by
  apply (reflectedUniformL2Equiv_coe L hL _).trans
  apply (reflectedUniformLaw_ae_iff L hL _).mp
  rw [reflectedCosineHilbertBasis_apply]
  exact reflectedL2Cosine_coe L hL n

theorem reflectedNeumann_cosine_graph (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (n : ℕ) :
    (reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n),
      reflectedCosinePhysicalRate L D n •
        reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n)) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph := by
  apply (reflectedNeumann_operator_graph_iff L hL D hD _ _).mpr
  refine ⟨reflectedNormalizedCosine L n, reflectedNormalizedCosineSlope L n,
    reflectedUniformL2Equiv_cosine_coe L hL n, ?_,
    (reflectedNormalizedCosine_neumann L hL n).1, (reflectedNormalizedCosine_neumann L hL n).2⟩
  have hr := reflectedNormalizedCosine_regularity L hL n
  refine ⟨hr.state_energy, hr.slope_energy, hr.slope_ae, hr.second_ae.trans ?_⟩
  filter_upwards [Lp.coeFn_smul (reflectedCosinePhysicalRate L D n)
    (reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n)),
    reflectedUniformL2Equiv_cosine_coe L hL n] with x hx hy
  rw [hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hy]
  unfold reflectedCosinePhysicalRate
  field_simp [hD.ne']

theorem reflectedNeumann_finite_cosine_graph (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ s, c n • reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n),
      ∑ n ∈ s, (reflectedCosinePhysicalRate L D n * c n) •
        reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n)) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph := by
  rw [prod_mk_sum]
  apply Submodule.sum_mem
  intro n _
  simpa only [Prod.smul_mk, smul_smul, mul_comm] using
    (reflectedNeumannProblem L hL D hD).operator.graph.smul_mem (c n)
      (reflectedNeumann_cosine_graph L hL D hD n)

end TimeTraps.Probability

end
