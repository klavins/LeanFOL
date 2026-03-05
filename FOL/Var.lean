--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace FOL

/-
Variables
===
-/

abbrev Arity := ℕ
abbrev Var := ℕ
abbrev Level := ℕ

def Var.shift (level : Level) (v : Var) : Var :=
  if v < level then v else v + 1

def Var.unshift (level : Level) (v : Var) : Var :=
  if v < level then v else v - 1

def Var.subst (s x : Var) (v : Var) : Var :=
  if v = x then s else v

notation:max t "[" x " ↦ " s "]" => Var.subst s x t

def Var.inst_at (t : Var) (level : Level) (v : Var) : Var :=
  if v < level then v
  else if v = level then t
  else v - 1

section

namespace Var

variable {level : Level} {t v s s' x y : Var}

@[simp]
theorem unshift_shift  : unshift level ∘ shift level = id := by
  funext v
  simp[shift,unshift]
  split_ifs with h1 h2
  · rfl
  · have h3 : level < level := by
      have h4 : v < v + 1 := lt_add_one v
      have h5 : v < level := Nat.lt_trans h4 h2
      exact False.elim (h1 h5)
    exact False.elim ((lt_self_iff_false level).mp h3)
  · exact add_tsub_cancel_right _ _

@[simp]
theorem subst_eq : x[x↦s] = s := by
  simp[subst]

@[simp]
theorem subst_ne (h : t ≠ x) : t[x↦s] = t := by
  simp[subst, h]

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x): v[x↦s][y↦t] = v[y↦t][x↦s[y↦t]] := by
  simp[subst]
  aesop

@[simp]
theorem subst_succ_ne_succ (h : t ≠ x) : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by
  simp[subst, h]

@[simp]
theorem subst_succ : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by
  by_cases h : t = x <;> simp [h]

@[simp]
theorem inst_at_lt (h : v < level) :  inst_at t level v = v := by
  simp [inst_at, h]

@[simp]
theorem inst_at_eq : inst_at t level level = t := by
  simp [inst_at]

@[simp]
theorem inst_at_gt (h : level < v) : inst_at t level v = v - 1 := by
  simp [inst_at, not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]

@[simp] theorem subst_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x ↦ s] = v := subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hx))

@[simp] theorem subst_succ_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x+1 ↦ s+1] = v := subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv (Nat.le_succ_of_le hx)))

@[simp] theorem inst_at_succ_of_le (hs : level ≤ s) : inst_at t level (s + 1) = s := by
  simp [inst_at_gt (Nat.lt_succ_of_le hs)]

@[simp] theorem inst_at_shift : inst_at t level (Var.shift level v) = v := by
  by_cases h : v < level
  · simp [Var.shift, h]
  · simp [Var.shift, h, inst_at_succ_of_le (Nat.le_of_not_lt h)]

@[simp] theorem subst_pred_of_gt_of_ne (hgt : level < v) (hne : v ≠ x + 1)
  : (v - 1)[x ↦ s] = v - 1 := by
  apply subst_ne
  intro heq
  exact hne (Nat.eq_add_of_sub_eq (Nat.lt_of_le_of_lt (Nat.zero_le level) hgt) heq)

theorem subst_inst_at (hs : level ≤ s) (hx : level ≤ x) :
    (inst_at t level v)[x ↦ s] = inst_at (t[x ↦ s]) level (v[x+1 ↦ s+1]) := by
  by_cases h1 : v < level
  · simp [subst_of_lt_of_le h1 hx, subst_succ_of_lt_of_le h1 hx, inst_at_lt h1]
  by_cases h2 : v = level
  · simp [*,subst_ne (Nat.ne_of_lt (hx.trans_lt (Nat.lt_succ_self x))), inst_at_eq]
  · have h3 : v ≥ level := Nat.le_of_not_lt h1
    have hgt : level < v := Nat.lt_of_le_of_ne h3 (Ne.symm h2)
    rw [inst_at_gt hgt]
    by_cases h4 : v = x + 1
    · subst h4
      simp [subst_eq, inst_at_succ_of_le hs]
    · rw [subst_pred_of_gt_of_ne hgt h4, subst_ne h4, inst_at_gt hgt]

end Var
end -- section
end FOL
