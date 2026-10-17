module

public import TimeTraps.Analysis.ReflectedInteriorTanakaRepresentation
public import TimeTraps.Analysis.ReflectedInteriorTanakaSlopeGeometry
public import TimeTraps.Analysis.FiniteKinkCalculus
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! An explicit finite labelled-kink encoding of the checked symmetric
approximants. The signed coefficient sum works for arbitrary scalar data,
so it also identifies the actual affine local-time correction sum. -/

noncomputable section

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability

def reflectedInteriorFiniteSet (N : ℕ) : Finset (Fin 3 ⊕ (ℕ × Fin 8)) :=
  Finset.univ.disjSum ((Finset.range N) ×ˢ Finset.univ)

def reflectedInteriorFiniteSite (L a : ℝ) : Fin 3 ⊕ (ℕ × Fin 8) → ℝ :=
  Sum.elim ![0, a, -a] (fun p =>
    ![((2 * (p.1 + 1) : ℕ) * L - a), -((2 * (p.1 + 1) : ℕ) * L - a),
      ((2 * (p.1 + 1) : ℕ) * L + a), -((2 * (p.1 + 1) : ℕ) * L + a),
      ((2 * p.1 + 1 : ℕ) * L), -((2 * p.1 + 1 : ℕ) * L),
      ((2 * (p.1 + 1) : ℕ) * L), -((2 * (p.1 + 1) : ℕ) * L)] p.2)

def reflectedInteriorFiniteCoeff : Fin 3 ⊕ (ℕ × Fin 8) → ℝ :=
  Sum.elim ![-1, 1, 1] (fun p => ![1, 1, 1, 1, -1, -1, -1, -1] p.2)

theorem reflectedInteriorFinite_sum (L a : ℝ) (N : ℕ) (f : ℝ → ℝ) :
    (∑ i ∈ reflectedInteriorFiniteSet N, reflectedInteriorFiniteCoeff i * f (reflectedInteriorFiniteSite L a i)) =
      -f 0 + f a + f (-a) + ∑ j ∈ Finset.range N,
        (f ((2 * (j + 1) : ℕ) * L - a) + f (-((2 * (j + 1) : ℕ) * L - a)) +
          f ((2 * (j + 1) : ℕ) * L + a) + f (-((2 * (j + 1) : ℕ) * L + a)) -
          f ((2 * j + 1 : ℕ) * L) - f (-((2 * j + 1 : ℕ) * L)) -
          f ((2 * (j + 1) : ℕ) * L) - f (-((2 * (j + 1) : ℕ) * L))) := by
  simp only [reflectedInteriorFiniteSet, Finset.sum_disjSum, Finset.sum_product,
    reflectedInteriorFiniteCoeff, reflectedInteriorFiniteSite, Sum.elim_inl, Sum.elim_inr]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_mul, neg_one_mul, add_zero]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem reflectedInteriorFinite_slope (L a : ℝ) (N : ℕ) (z : ℝ) :
    finiteKinkSlope (fun _ => (0 : ℝ)) (reflectedInteriorFiniteSet N)
      (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff z =
      reflectedInteriorTanakaSlopeApprox L a N z := by
  rw [finiteKinkSlope, deriv_const, zero_add,
    reflectedInteriorFinite_sum L a N (fun q => Real.sign (z - q))]
  simp only [reflectedInteriorTanakaSlopeApprox, symmetricSignPair, sub_zero, sub_neg_eq_add]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem reflectedInteriorFinite_difference (L a : ℝ) (N : ℕ) (z w : ℝ) :
    finiteKinkPotential (fun _ => (0 : ℝ)) (reflectedInteriorFiniteSet N)
        (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff z -
      finiteKinkPotential (fun _ => (0 : ℝ)) (reflectedInteriorFiniteSet N)
        (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff w =
      reflectedInteriorTanakaApprox L a N z - reflectedInteriorTanakaApprox L a N w := by
  simp only [finiteKinkPotential, zero_add]
  rw [reflectedInteriorFinite_sum L a N (fun q => |z - q|),
    reflectedInteriorFinite_sum L a N (fun q => |w - q|)]
  simp only [reflectedInteriorTanakaApprox, symmetricAbsPair, sub_zero, sub_neg_eq_add]
  have hs : (∑ j ∈ Finset.range N,
      (|z - ((2 * (j + 1) : ℕ) * L - a)| + |z + ((2 * (j + 1) : ℕ) * L - a)| +
        |z - ((2 * (j + 1) : ℕ) * L + a)| + |z + ((2 * (j + 1) : ℕ) * L + a)| -
        |z - (2 * j + 1 : ℕ) * L| - |z + (2 * j + 1 : ℕ) * L| -
        |z - (2 * (j + 1) : ℕ) * L| - |z + (2 * (j + 1) : ℕ) * L|)) -
      (∑ j ∈ Finset.range N,
      (|w - ((2 * (j + 1) : ℕ) * L - a)| + |w + ((2 * (j + 1) : ℕ) * L - a)| +
        |w - ((2 * (j + 1) : ℕ) * L + a)| + |w + ((2 * (j + 1) : ℕ) * L + a)| -
        |w - (2 * j + 1 : ℕ) * L| - |w + (2 * j + 1 : ℕ) * L| -
        |w - (2 * (j + 1) : ℕ) * L| - |w + (2 * (j + 1) : ℕ) * L|)) =
      (∑ j ∈ Finset.range N,
        (symmetricAbsPair ((2 * (j + 1) : ℕ) * L - a) z +
          symmetricAbsPair ((2 * (j + 1) : ℕ) * L + a) z -
          symmetricAbsPair ((2 * j + 1 : ℕ) * L) z -
          symmetricAbsPair ((2 * (j + 1) : ℕ) * L) z)) -
      (∑ j ∈ Finset.range N,
        (symmetricAbsPair ((2 * (j + 1) : ℕ) * L - a) w +
          symmetricAbsPair ((2 * (j + 1) : ℕ) * L + a) w -
          symmetricAbsPair ((2 * j + 1 : ℕ) * L) w -
          symmetricAbsPair ((2 * (j + 1) : ℕ) * L) w)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold symmetricAbsPair
    ring
  simp only [symmetricAbsPair] at hs
  linear_combination hs

end TimeTraps.Analysis

end
