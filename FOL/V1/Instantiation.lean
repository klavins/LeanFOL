--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import FOL.V1.Var
import FOL.V1.Tuple
import FOL.V1.Formula
import FOL.V1.Rename

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false

/-
Inst at for Formulas
===
-/

def Formula.inst_at {S : Signature} (t : Var) (level : Level) : Formula S → Formula S
  | Formula.bot         => Formula.bot
  | Formula.rel r tuple => Formula.rel r (tuple.inst_at level t)
  | Formula.imp φ ψ     => Formula.imp (inst_at t level φ) (inst_at t level ψ)
  | Formula.all φ       => Formula.all (inst_at (t+1) (level+1) φ)

def Formula.inst {S : Signature} (t : Var) : Formula S → Formula S := inst_at t 0

section

namespace Formula

variable {S : Signature} {φ ψ : Formula S} {s x y t : Var} {level : Level}

@[simp] theorem inst_eq : φ.inst t = φ.inst_at t 0 := rfl

@[simp] theorem inst_at_bot : (bot : Formula S).inst_at t level = bot := rfl

@[simp] theorem inst_at_imp
  : (imp φ ψ).inst_at t level = imp (φ.inst_at t level) (ψ.inst_at t level) := rfl

@[simp] theorem inst_at_all
  : (all φ).inst_at t level = all (φ.inst_at (t+1) (level+1)) := rfl

@[simp] theorem inst_at_rel {k : Arity} {r : S k} {τ : Tuple k}
  : (rel r τ).inst_at t level = rel r (τ.inst_at level t) := rfl

theorem inst_at_subst (h₁ : level ≤ x) (h₂ : level ≤ s)
  : (φ.inst_at t level)[x↦s] = φ[x+1↦s+1].inst_at t[x↦s] level := by
  induction φ generalizing t s level x with
  | bot => rfl
  | rel t τ => simp[*]
  | imp f g ihf ihg => simp[*]
  | all f ih =>
      simp [ih (Nat.succ_le_succ h₁) (Nat.succ_le_succ h₂)]

theorem inst_subst {S : Signature} (φ : Formula S) (s x t : Var)
  : (φ.inst t)[x↦s] = φ[x+1↦s+1].inst t[x↦s]  := by
  exact inst_at_subst (Nat.zero_le x) (Nat.zero_le s)

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : φ[x↦s][y↦t] = φ[y↦t][x↦s[y↦t]] := by
  induction φ generalizing t s x y with
  | bot => rfl
  | rel r τ => simp[subst, *]
  | imp f g ihf ihg => simp[subst, *]
  | all f ih =>
    have := @ih (s+1) (x+1) (y+1) (t+1)
                ((add_ne_add_left 1).mpr h₁) (
                (add_ne_add_left 1).mpr h₂)
    simp[this]

@[simp] theorem subst_id : φ[x↦x] = φ := by
  induction φ generalizing x <;> simp[*]

@[simp] theorem inst_shift : (φ.shift).inst x = φ := by
  suffices h : ∀ (level : Level),
               (φ.rename (Var.shift level)).inst_at x level = φ from h 0
  induction φ generalizing x with
  | bot => intros; rfl
  | rel r τ =>
    intros
    simp [rename]
    exact Tuple.inst_at_shift
  | imp f g ihf ihg => simp [rename, ihf, ihg]
  | all f ih => simp [rename, ih]

theorem inst_at_eq_rename : φ.inst_at t level = φ.rename (Var.inst_at t level) := by
  induction φ generalizing t level with
  | bot => rfl
  | rel r τ => simp[Formula.inst_at, Formula.rename, Tuple.inst_at]
  | imp g h ihg ihh => simp[Formula.inst_at, Formula.rename, ihg, ihh]
  | all g ih =>
    simp only [Formula.inst_at, Formula.rename]
    simp[lift_inst_at]
    exact ih

end Formula
end
end FOL
