module

public import TimeTraps.Interval.ClosedPartition

@[expose] public section

/-! Uniform widths determine the entire ordered partition, including all
endpoint coordinates. The converse is exact finite telescoping. -/

namespace TimeTraps.Interval

variable {n : ℕ}

theorem StrictPartition.uniform_point (hn : 0 < n) (e : Fin (n + 1)) :
    (StrictPartition.uniform n hn).point e = (e.val : ℝ) / n := rfl

theorem StrictPartition.uniform_width (hn : 0 < n) (i : Fin n) :
    (StrictPartition.uniform n hn).width i = 1 / (n : ℝ) := by
  change ((i.val + 1 : ℕ) : ℝ) / n - (i.val : ℝ) / n = _
  rw [Nat.cast_add, Nat.cast_one]
  ring

theorem ClosedPartition.point_of_uniform_width (Q : ClosedPartition n)
    (hw : ∀ i, Q.width i = 1 / (n : ℝ)) (e : Fin (n + 1)) :
    Q.point e = (e.val : ℝ) / n := by
  induction e using Fin.induction with
  | zero => simpa only [Fin.val_zero, Nat.cast_zero, zero_div] using Q.first
  | succ i ih =>
    have hi := hw i
    change Q.point i.castSucc = (i.val : ℝ) / n at ih
    change Q.point i.succ - Q.point i.castSucc = 1 / (n : ℝ) at hi
    change Q.point i.succ = ((i.val + 1 : ℕ) : ℝ) / n
    rw [Nat.cast_add, Nat.cast_one, add_div]
    linarith

theorem ClosedPartition.eq_uniform_of_width (Q : ClosedPartition n) (hn : 0 < n)
    (hw : ∀ i, Q.width i = 1 / (n : ℝ)) : Q = (StrictPartition.uniform n hn).closed := by
  apply Subtype.ext
  funext e
  exact Q.point_of_uniform_width hw e

theorem StrictPartition.eq_of_point_eq (Q P : StrictPartition n) (h : Q.point = P.point) : Q = P := by
  cases Q
  cases P
  dsimp only at h
  cases h
  rfl

theorem StrictPartition.eq_uniform_of_width (Q : StrictPartition n) (hn : 0 < n)
    (hw : ∀ i, Q.width i = 1 / (n : ℝ)) : Q = StrictPartition.uniform n hn := by
  apply Q.eq_of_point_eq
  funext e
  exact Q.closed.point_of_uniform_width hw e

end TimeTraps.Interval
