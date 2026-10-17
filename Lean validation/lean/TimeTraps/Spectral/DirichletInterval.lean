module

public import TimeTraps.Analysis.IntervalEnergy

@[expose] public section

/-!
The independent empty-cell spectral problem with one or two perfectly
absorbing endpoints. Admissibility is defined by H1 membership and the
specified zero traces. A reflecting endpoint imposes no trace restriction
on competitors. No eigenfunction or spectral value is built into the data.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

inductive AbsorbingEnds where
  | left
  | right
  | both

structure DirichletInterval where
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  ends : AbsorbingEnds

def DirichletInterval.zeroTraces (P : DirichletInterval) (v : ℝ → ℝ) : Prop :=
  match P.ends with
  | .left => v 0 = 0
  | .right => v P.length = 0
  | .both => v 0 = 0 ∧ v P.length = 0

def DirichletInterval.admissible (P : DirichletInterval) (v : ℝ → ℝ) : Prop :=
  IntervalEnergy v 0 P.length ∧ P.zeroTraces v

noncomputable def DirichletInterval.quadraticForm (P : DirichletInterval) (v : ℝ → ℝ) : ℝ :=
  P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv v x ^ 2)

noncomputable def DirichletInterval.squareMass (P : DirichletInterval) (v : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..P.length, v x ^ 2

def DirichletInterval.rayleighValues (P : DirichletInterval) : Set ℝ :=
  {r | ∃ v : ℝ → ℝ, P.admissible v ∧ 0 < P.squareMass v ∧
    r = P.quadraticForm v / P.squareMass v}

noncomputable def DirichletInterval.principalValue (P : DirichletInterval) : ℝ :=
  sInf P.rayleighValues

structure DirichletWeakEigenEquation (P : DirichletInterval) (ev : ℝ) (u : ℝ → ℝ) : Prop where
  admissible : P.admissible u
  weak_form : ∀ v, P.admissible v →
    P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) =
      ev * (∫ x in (0 : ℝ)..P.length, u x * v x)

theorem DirichletInterval.quadraticForm_nonneg (P : DirichletInterval) (v : ℝ → ℝ) :
    0 ≤ P.quadraticForm v :=
  mul_nonneg P.diffusivity_pos.le
    (intervalIntegral.integral_nonneg P.length_pos.le (fun _ _ => sq_nonneg _))

theorem DirichletInterval.rayleighValues_bddBelow (P : DirichletInterval) :
    BddBelow P.rayleighValues := by
  refine ⟨0, ?_⟩
  rintro r ⟨v, _, hv, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg v) hv.le

theorem DirichletWeakEigenEquation.self_quadraticForm {P : DirichletInterval}
    {ev : ℝ} {u : ℝ → ℝ} (h : DirichletWeakEigenEquation P ev u) :
    P.quadraticForm u = ev * P.squareMass u := by
  simpa only [DirichletInterval.quadraticForm, DirichletInterval.squareMass, pow_two]
    using h.weak_form u h.admissible

end TimeTraps.Spectral
