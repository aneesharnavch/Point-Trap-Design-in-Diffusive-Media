module

public import TimeTraps.Interval.OrderedDesign
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Exact value-and-slope propagation for the homogeneous Poisson equation.
The final gap has no reaction update. The independent coefficient recurrence
proves affine dependence on the initial value and strict positivity of the
terminal slope coefficient when there is at least one positive trap.
-/

namespace TimeTraps.Interval

noncomputable def poissonGap (D h : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 + s.2 * h - h ^ 2 / (2 * D), s.2 - h / D)

noncomputable def poissonJump (D κ : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1, s.2 + κ * s.1 / D)

def poissonLinearGap (h : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 + s.2 * h, s.2)

variable {n : ℕ}

noncomputable def poissonRun (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (U : ℝ) (e : Fin (n + 1)) : ℝ × ℝ :=
  Fin.induction (U, 0) (fun i s => poissonJump D (κ i) (poissonGap D (gap i.castSucc) s)) e

noncomputable def poissonResponse (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (e : Fin (n + 1)) : ℝ × ℝ :=
  Fin.induction (1, 0)
    (fun i s => poissonJump D (κ i) (poissonLinearGap (gap i.castSucc) s)) e

theorem poissonRun_zero (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ) (U : ℝ) :
    poissonRun D gap κ U 0 = (U, 0) := rfl

theorem poissonRun_succ (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (U : ℝ) (i : Fin n) :
    poissonRun D gap κ U i.succ =
      poissonJump D (κ i) (poissonGap D (gap i.castSucc) (poissonRun D gap κ U i.castSucc)) := by
  simp only [poissonRun, Fin.induction_succ]

theorem poissonResponse_zero (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ) :
    poissonResponse D gap κ 0 = (1, 0) := rfl

theorem poissonResponse_succ (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (i : Fin n) :
    poissonResponse D gap κ i.succ =
      poissonJump D (κ i) (poissonLinearGap (gap i.castSucc) (poissonResponse D gap κ i.castSucc)) := by
  simp only [poissonResponse, Fin.induction_succ]

theorem poissonRun_affine (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (U : ℝ) (e : Fin (n + 1)) :
    poissonRun D gap κ U e =
      ((poissonRun D gap κ 0 e).1 + (poissonResponse D gap κ e).1 * U,
       (poissonRun D gap κ 0 e).2 + (poissonResponse D gap κ e).2 * U) := by
  induction e using Fin.induction with
  | zero => simp only [poissonRun_zero, poissonResponse_zero, one_mul, zero_add, zero_mul]
  | succ i ih =>
    rw [poissonRun_succ, ih, poissonRun_succ, poissonResponse_succ]
    apply Prod.ext <;> simp only [poissonGap, poissonJump, poissonLinearGap] <;> ring

theorem poissonResponse_positive (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (hD : 0 < D) (hgap : ∀ e, 0 ≤ gap e) (hκ : ∀ i, 0 < κ i) (e : Fin (n + 1)) :
    0 < (poissonResponse D gap κ e).1 ∧ 0 ≤ (poissonResponse D gap κ e).2 := by
  induction e using Fin.induction with
  | zero => simp only [poissonResponse_zero]; constructor <;> norm_num
  | succ i ih =>
    rw [poissonResponse_succ]
    have hu : 0 < (poissonResponse D gap κ i.castSucc).1 +
        (poissonResponse D gap κ i.castSucc).2 * gap i.castSucc :=
      add_pos_of_pos_of_nonneg ih.1 (mul_nonneg ih.2 (hgap i.castSucc))
    exact ⟨hu, (add_pos_of_nonneg_of_pos ih.2 (div_pos (mul_pos (hκ i) hu) hD)).le⟩

theorem poissonResponse_slope_pos (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (hD : 0 < D) (hgap : ∀ e, 0 ≤ gap e) (hκ : ∀ i, 0 < κ i)
    (e : Fin (n + 1)) (he : 0 < e.val) : 0 < (poissonResponse D gap κ e).2 := by
  cases e using Fin.cases with
  | zero => simp only [Fin.val_zero] at he; omega
  | succ i =>
    rw [poissonResponse_succ]
    have hi := poissonResponse_positive D gap κ hD hgap hκ i.castSucc
    have hu : 0 < (poissonResponse D gap κ i.castSucc).1 +
        (poissonResponse D gap κ i.castSucc).2 * gap i.castSucc :=
      add_pos_of_pos_of_nonneg hi.1 (mul_nonneg hi.2 (hgap i.castSucc))
    exact add_pos_of_nonneg_of_pos hi.2 (div_pos (mul_pos (hκ i) hu) hD)

noncomputable def poissonTerminal (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ) (U : ℝ) : ℝ × ℝ :=
  poissonGap D (gap (Fin.last n)) (poissonRun D gap κ U (Fin.last n))

noncomputable def poissonTerminalResponse (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ) : ℝ × ℝ :=
  poissonLinearGap (gap (Fin.last n)) (poissonResponse D gap κ (Fin.last n))

theorem poissonTerminal_affine (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ) (U : ℝ) :
    poissonTerminal D gap κ U =
      ((poissonTerminal D gap κ 0).1 + (poissonTerminalResponse D gap κ).1 * U,
       (poissonTerminal D gap κ 0).2 + (poissonTerminalResponse D gap κ).2 * U) := by
  unfold poissonTerminal poissonTerminalResponse
  rw [poissonRun_affine D gap κ U]
  apply Prod.ext <;> simp only [poissonGap, poissonLinearGap] <;> ring

theorem poissonTerminalResponse_positive (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (hD : 0 < D) (hgap : ∀ e, 0 ≤ gap e) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    0 < (poissonTerminalResponse D gap κ).1 ∧ 0 < (poissonTerminalResponse D gap κ).2 := by
  have hi := poissonResponse_positive D gap κ hD hgap hκ (Fin.last n)
  exact ⟨add_pos_of_pos_of_nonneg hi.1 (mul_nonneg hi.2 (hgap (Fin.last n))),
    poissonResponse_slope_pos D gap κ hD hgap hκ (Fin.last n) hn⟩

noncomputable def poissonInitial (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ) : ℝ :=
  -(poissonTerminal D gap κ 0).2 / (poissonTerminalResponse D gap κ).2

theorem poissonTerminal_reflecting_iff (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (hD : 0 < D) (hgap : ∀ e, 0 ≤ gap e) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) (U : ℝ) :
    (poissonTerminal D gap κ U).2 = 0 ↔ U = poissonInitial D gap κ := by
  have hd := ne_of_gt (poissonTerminalResponse_positive D gap κ hD hgap hκ hn).2
  rw [poissonTerminal_affine]
  change (poissonTerminal D gap κ 0).2 + (poissonTerminalResponse D gap κ).2 * U = 0 ↔ _
  rw [poissonInitial, eq_div_iff hd]
  constructor <;> intro he <;> linarith

theorem poissonInitial_reflecting (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (hD : 0 < D) (hgap : ∀ e, 0 ≤ gap e) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    (poissonTerminal D gap κ (poissonInitial D gap κ)).2 = 0 :=
  (poissonTerminal_reflecting_iff D gap κ hD hgap hκ hn _).mpr rfl

theorem poisson_reflecting_existsUnique (D : ℝ) (gap : Fin (n + 1) → ℝ) (κ : Fin n → ℝ)
    (hD : 0 < D) (hgap : ∀ e, 0 ≤ gap e) (hκ : ∀ i, 0 < κ i) (hn : 0 < n) :
    ∃! U, (poissonTerminal D gap κ U).2 = 0 :=
  ⟨poissonInitial D gap κ, poissonInitial_reflecting D gap κ hD hgap hκ hn,
    fun U hU => (poissonTerminal_reflecting_iff D gap κ hD hgap hκ hn U).mp hU⟩

end TimeTraps.Interval
