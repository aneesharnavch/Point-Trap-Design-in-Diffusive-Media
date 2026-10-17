module

public import TimeTraps.Probability.BrownianIntegralMaximalPathwise
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! The finite L² maximal inequality for nonnegative real submartingales.
The proof uses adapted square-integrable running maxima as weights, the
conditional-expectation pull-out property, and Cauchy--Schwarz. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {𝒢 : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem finiteRunningMax_stronglyAdapted (hX : StronglyAdapted 𝒢 X) :
    StronglyAdapted 𝒢 (fun n ω => finiteRunningMax (fun k => X k ω) n) := by
  intro n
  induction n with
  | zero => exact hX 0
  | succ n ih =>
    let : MeasurableSpace Ω := 𝒢 (n + 1)
    exact (ih.mono (𝒢.mono (Nat.le_succ n))).sup (hX (n + 1))

theorem finiteRunningMax_memLp (hX : ∀ n, MemLp (X n) 2 P) (n : ℕ) :
    MemLp (fun ω => finiteRunningMax (fun k => X k ω) n) 2 P := by
  induction n with
  | zero => exact hX 0
  | succ n ih => exact ih.sup (hX (n + 1))

theorem submartingale_weighted_integral_le [IsFiniteMeasure P] (hX : Submartingale X 𝒢 P)
    {i j : ℕ} (hij : i ≤ j) {w : Ω → ℝ} (hw : StronglyMeasurable[𝒢 i] w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw2 : MemLp w 2 P)
    (hi2 : MemLp (X i) 2 P) (hj2 : MemLp (X j) 2 P) :
    (∫ ω, w ω * X i ω ∂P) ≤ ∫ ω, w ω * X j ω ∂P := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hw
    (hw2.integrable_mul hj2) (hX.integrable j)
  have hpullInt : Integrable (fun ω => w ω * P[X j | 𝒢 i] ω) P :=
    integrable_condExp.congr hpull
  calc
    _ ≤ ∫ ω, w ω * P[X j | 𝒢 i] ω ∂P := by
      apply integral_mono_ae (hw2.integrable_mul hi2) hpullInt
      filter_upwards [hX.ae_le_condExp hij] with ω hω
      exact mul_le_mul_of_nonneg_left hω (hw0 ω)
    _ = ∫ ω, P[fun ω => w ω * X j ω | 𝒢 i] ω ∂P :=
      (integral_congr_ae hpull).symm
    _ = _ := integral_condExp (𝒢.le i)

theorem nonnegative_submartingale_maximal_pairing [IsFiniteMeasure P]
    (hX : Submartingale X 𝒢 P) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hX2 : ∀ n, MemLp (X n) 2 P) (n : ℕ) :
    (∫ ω, finiteRunningMax (fun k => X k ω) n ^ 2 ∂P) ≤
      2 * ∫ ω, X n ω * finiteRunningMax (fun k => X k ω) n ∂P := by
  let R : ℕ → Ω → ℝ := fun k ω => finiteRunningMax (fun j => X j ω) k
  let D : ℕ → Ω → ℝ := fun k ω => R k ω * (X (k + 1) ω - X k ω)
  have hR2 (k : ℕ) : MemLp (R k) 2 P := finiteRunningMax_memLp hX2 k
  have hR0 (k : ℕ) (ω : Ω) : 0 ≤ R k ω :=
    finiteRunningMax_nonneg (fun j => X j ω) (hX0 0 ω) k
  have hDint (k : ℕ) : Integrable (D k) P :=
    (hR2 k).integrable_mul ((hX2 (k + 1)).sub (hX2 k))
  have hD0 (k : ℕ) : 0 ≤ ∫ ω, D k ω ∂P := by
    have h := submartingale_weighted_integral_le hX (Nat.le_succ k)
      (finiteRunningMax_stronglyAdapted hX.stronglyAdapted k) (hR0 k)
      (hR2 k) (hX2 k) (hX2 (k + 1))
    have he : (∫ ω, D k ω ∂P) =
        (∫ ω, R k ω * X (k + 1) ω ∂P) - ∫ ω, R k ω * X k ω ∂P := by
      simp only [D, mul_sub]
      exact integral_sub ((hR2 k).integrable_mul (hX2 (k + 1)))
        ((hR2 k).integrable_mul (hX2 k))
    rw [he]
    exact sub_nonneg.mpr h
  have hsumInt : Integrable (fun ω => ∑ k ∈ Finset.range n, D k ω) P :=
    integrable_finsetSum _ (fun k _ => hDint k)
  have hprodInt : Integrable (fun ω => X n ω * R n ω) P :=
    (hX2 n).integrable_mul (hR2 n)
  have hpath : (∫ ω, R n ω ^ 2 ∂P) ≤
      ∫ ω, 2 * (X n ω * R n ω) - 2 * (∑ k ∈ Finset.range n, D k ω) ∂P := by
    apply integral_mono (hR2 n).integrable_sq
      ((hprodInt.const_mul 2).sub (hsumInt.const_mul 2))
    intro ω
    change R n ω ^ 2 ≤ 2 * (X n ω * R n ω) - 2 * (∑ k ∈ Finset.range n, D k ω)
    simpa only [R, D, mul_assoc] using finiteRunningMax_sq_le (fun k => X k ω) n
  rw [integral_sub (hprodInt.const_mul 2) (hsumInt.const_mul 2),
    integral_const_mul, integral_const_mul, integral_finsetSum _ (fun k _ => hDint k)] at hpath
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range n, ∫ ω, D k ω ∂P :=
    Finset.sum_nonneg (fun k _ => hD0 k)
  change (∫ ω, R n ω ^ 2 ∂P) ≤ 2 * ∫ ω, X n ω * R n ω ∂P
  linarith

theorem nonnegative_submartingale_maximal_L2 [IsFiniteMeasure P]
    (hX : Submartingale X 𝒢 P) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hX2 : ∀ n, MemLp (X n) 2 P) (n : ℕ) :
    (∫ ω, finiteRunningMax (fun k => X k ω) n ^ 2 ∂P) ≤ 4 * ∫ ω, X n ω ^ 2 ∂P := by
  let A := ∫ ω, finiteRunningMax (fun k => X k ω) n ^ 2 ∂P
  let C := ∫ ω, X n ω * finiteRunningMax (fun k => X k ω) n ∂P
  let Q := ∫ ω, X n ω ^ 2 ∂P
  have hA : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
  have hC : 0 ≤ C := integral_nonneg (fun ω => mul_nonneg (hX0 n ω)
    (finiteRunningMax_nonneg _ (hX0 0 ω) n))
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  have hp : A ≤ 2 * C := nonnegative_submartingale_maximal_pairing hX hX0 hX2 n
  have hcs : C ^ 2 ≤ Q * A := TimeTraps.Analysis.memLp_integral_mul_sq_le
    (hX2 n) (finiteRunningMax_memLp hX2 n)
  have hsq : A ^ 2 ≤ (2 * C) ^ 2 := (sq_le_sq₀ hA (by positivity)).mpr hp
  change A ≤ 4 * Q
  by_cases hAz : A = 0
  · rw [hAz]
    positivity
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hmul : A * A ≤ A * (4 * Q) := by nlinarith
    exact le_of_mul_le_mul_left hmul hAp

theorem martingale_abs_submartingale (hX : Martingale X 𝒢 P) :
    Submartingale (fun n ω => |X n ω|) 𝒢 P := by
  refine ⟨?_, ?_, fun n => (hX.integrable n).abs⟩
  · intro n
    let : MeasurableSpace Ω := 𝒢 n
    simpa only [Real.norm_eq_abs] using (hX.stronglyMeasurable n).norm
  · intro i j hij
    have he : |X j| = fun ω => |X j ω| := rfl
    filter_upwards [hX.condExp_ae_eq hij, abs_condExp_ae_le_condExp_abs (X j) (m := 𝒢 i)]
      with ω hω hnorm
    rw [he] at hnorm
    simpa only [Pi.abs_apply, hω] using hnorm

end TimeTraps.Probability
