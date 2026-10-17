module

public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! Exact third absolute moment bounds from the actual second and fourth
moments. The proof is Cauchy--Schwarz in L2 for |X| and X squared. -/

namespace TimeTraps.Analysis

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

theorem memLp_integrable_abs_cube (hX : MemLp X 2 μ)
    (hX₂ : MemLp (fun ω => X ω ^ 2) 2 μ) : Integrable (fun ω => |X ω| ^ 3) μ := by
  have hA : MemLp (fun ω => |X ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hX.norm
  have he (x : ℝ) : |x| * x ^ 2 = |x| ^ 3 := by rw [← sq_abs x]; ring
  have hi := hA.integrable_mul hX₂
  change Integrable (fun ω => |X ω| * X ω ^ 2) μ at hi
  simpa only [he] using hi

theorem memLp_integral_abs_cube_sq_le (hX : MemLp X 2 μ)
    (hX₂ : MemLp (fun ω => X ω ^ 2) 2 μ) :
    (∫ ω, |X ω| ^ 3 ∂μ) ^ 2 ≤ (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, X ω ^ 4 ∂μ) := by
  have hA : MemLp (fun ω => |X ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hX.norm
  have he (x : ℝ) : |x| * x ^ 2 = |x| ^ 3 := by rw [← sq_abs x]; ring
  simpa only [he, sq_abs, ← pow_mul, Nat.reduceMul] using memLp_integral_mul_sq_le hA hX₂

theorem memLp_integral_abs_cube_le (hX : MemLp X 2 μ)
    (hX₂ : MemLp (fun ω => X ω ^ 2) 2 μ) :
    (∫ ω, |X ω| ^ 3 ∂μ) ≤ Real.sqrt ((∫ ω, X ω ^ 2 ∂μ) * (∫ ω, X ω ^ 4 ∂μ)) :=
  Real.le_sqrt_of_sq_le (memLp_integral_abs_cube_sq_le hX hX₂)

end TimeTraps.Analysis
