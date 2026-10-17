module

public import TimeTraps.Interval.OrderedFlux
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
The exact squared-CDF error is a sum of cubic cell moments and nonnegative
displacement squares. The finite algebra uses signed interval integrals, so
it needs only total mass one; ordered sites and positive shares are imposed
when applying it to a physical design.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

def cdfNode (x : Fin n → ℝ) : Fin (n + 2) → ℝ := Fin.cons 0 (Fin.snoc x 1)

noncomputable def cdfSquareScore (p x : Fin n → ℝ) : ℝ :=
  ∑ e : Fin (n + 1), ∫ z in cdfNode x e.castSucc..cdfNode x e.succ,
    (absorptionPrefix p e - z) ^ 2

theorem cdfNode_first (x : Fin n → ℝ) : cdfNode x 0 = 0 := rfl

theorem cdfNode_last (x : Fin n → ℝ) : cdfNode x (Fin.last (n + 1)) = 1 := by
  simp [cdfNode]

theorem cdfNode_site (x : Fin n → ℝ) (i : Fin n) : cdfNode x i.castSucc.succ = x i := by
  simp [cdfNode]

theorem cdfNode_site' (x : Fin n → ℝ) (i : Fin n) : cdfNode x i.succ.castSucc = x i := by
  simpa only [Fin.succ_castSucc] using cdfNode_site x i

theorem cdf_square_gap_integral (q a b : ℝ) :
    (∫ z in a..b, (q - z) ^ 2) = ((b - q) ^ 3 - (a - q) ^ 3) / 3 := by
  have hd (z : ℝ) : HasDerivAt (fun t : ℝ => (t - q) ^ 3 / 3) ((q - z) ^ 2) z := by
    have h := ((((hasDerivAt_id z).sub_const q).pow 3).div_const 3)
    have he : ((3 : ℝ) * (z - q) ^ (3 - 1) * 1) / 3 = (q - z) ^ 2 := by ring
    change HasDerivAt (fun t : ℝ => (t - q) ^ 3 / 3)
      (((3 : ℝ) * (z - q) ^ (3 - 1) * 1) / 3) z at h
    rwa [he] at h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z)
    (((continuous_const.sub continuous_id).pow 2).intervalIntegrable a b)
  rw [hi]
  ring

theorem cdf_cubic_jump (p q x : ℝ) :
    ((x - q) ^ 3 - (x - (q + p)) ^ 3) / 3 =
      p ^ 3 / 12 + p * (x - (q + (q + p)) / 2) ^ 2 := by
  ring

theorem cdfSquareScore_identity (p x : Fin n → ℝ) (hp : ∑ i, p i = 1) :
    cdfSquareScore p x =
      ∑ i, (p i ^ 3 / 12 + p i *
        (x i - (absorptionPrefix p i.castSucc + absorptionPrefix p i.succ) / 2) ^ 2) := by
  let A (e : Fin (n + 1)) := (cdfNode x e.castSucc - absorptionPrefix p e) ^ 3 / 3
  let B (e : Fin (n + 1)) := (cdfNode x e.succ - absorptionPrefix p e) ^ 3 / 3
  have hscore : cdfSquareScore p x = ∑ e, (B e - A e) := by
    unfold cdfSquareScore
    apply Finset.sum_congr rfl
    intro e _
    rw [cdf_square_gap_integral]
    dsimp [A, B]
    ring
  have hA : A 0 = 0 := by simp [A, cdfNode_first, absorptionPrefix_zero]
  have hB : B (Fin.last n) = 0 := by
    simp [B, cdfNode_last, absorptionPrefix_last, hp]
  have hsum : (∑ e, (B e - A e)) = ∑ i : Fin n, (B i.castSucc - A i.succ) := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc B, Fin.sum_univ_succ A, hA, hB,
      Finset.sum_sub_distrib]
    ring
  rw [hscore, hsum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [A, B]
  rw [cdfNode_site, absorptionPrefix_succ]
  nlinarith only [cdf_cubic_jump (p i) (absorptionPrefix p i.castSucc) (x i)]

end TimeTraps.Interval
