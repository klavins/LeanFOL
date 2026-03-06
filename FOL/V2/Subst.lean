--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import FOL.V2.Defs

namespace FOL2

set_option linter.style.setOption false
set_option linter.flexible false

/-!
# Substitution
-/

def Var.subst (s x : Var) (v : Var) : Var :=
  if v = x then s else v

def Tuple.subst {k} (s x : Var) (tuple : Tuple k) : Tuple k :=
  (Var.subst s x) ∘ tuple

def Formula.subst {S : Signature} (t : Var) (x : Var) : Formula S → Formula S
  | bot => bot
  | rel r tuple => rel r (Tuple.subst t x tuple)
  | imp φ ψ => imp (subst t x φ) (subst t x ψ)
  | all φ => all (subst (t+1) (x+1) φ)

class Subst (α : Type*) where
  subst : Var → Var → α → α

notation:max t "[" x " ↦ " s "]" => Subst.subst s x t

instance Var.subst_inst : Subst Var := ⟨Var.subst⟩
instance Tuple.subst_inst {k} : Subst (Tuple k) := ⟨Tuple.subst⟩
instance Formula.subst_inst {S} : Subst (Formula S) := ⟨Formula.subst⟩

/-
Substitution Theorems
===
-/

section

variable {level : Level} {t v s s' x y : Var} {k : Arity} {τ : Tuple k}

@[simp] theorem Var.subst_inst_eq (s x v : Var)
  : Subst.subst s x v = Var.subst s x v := rfl

@[simp] theorem Tuple.subst_inst_eq {k} (s x : Var) (τ : Tuple k)
  : Subst.subst s x τ = Tuple.subst s x τ := rfl

@[simp] theorem Formula.subst_inst_eq {S} (s x : Var) (φ : Formula S)
  : Subst.subst s x φ = Formula.subst s x φ := rfl

namespace Var

@[simp] theorem subst_eq : x[x↦s] = s := by
  simp[subst]

@[simp] theorem subst_ne (h : t ≠ x) : t[x↦s] = t := by
  simp[subst, h]

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x) : v[x↦s][y↦t] = v[y↦t][x↦s[y↦t]] := by
  simp[subst]
  aesop

@[simp] theorem subst_succ_ne_succ (h : t ≠ x) : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by
  simp[subst, h]

@[simp] theorem subst_succ : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by
  by_cases h : t = x <;> simp [h,subst]

@[simp] theorem subst_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x ↦ s] = v := subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hx))

@[simp] theorem subst_succ_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x+1 ↦ s+1] = v := subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv (Nat.le_succ_of_le hx)))

@[simp] theorem subst_pred_of_gt_of_ne (hgt : level < v) (hne : v ≠ x + 1)
  : (v - 1)[x ↦ s] = v - 1 := by
  apply subst_ne
  intro heq
  exact hne (Nat.eq_add_of_sub_eq (Nat.lt_of_le_of_lt (Nat.zero_le level) hgt) heq)

@[simp]
theorem inst_at_lt (h : v < level) :  inst_at t level v = v := by
  simp [inst_at, h]

/-
Theorems Relating Substitution and Instantiation
===
-/

@[simp]
theorem inst_at_eq : inst_at t level level = t := by
  simp [inst_at]

@[simp]
theorem inst_at_gt (h : level < v) : inst_at t level v = v - 1 := by
  simp [inst_at, not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]

@[simp] theorem inst_at_succ_of_le (hs : level ≤ s) : inst_at t level (s + 1) = s := by
  simp [inst_at_gt (Nat.lt_succ_of_le hs)]

@[simp] theorem inst_at_shift : inst_at t level (Var.shift level v) = v := by
  by_cases h : v < level
  · simp [Var.shift, h]
  · simp [Var.shift, h, inst_at_succ_of_le (Nat.le_of_not_lt h)]

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
      simp [subst, inst_at_succ_of_le hs]
    · rw [subst_pred_of_gt_of_ne hgt h4, subst_ne h4, inst_at_gt hgt]

end Var

end


section

namespace Formula

variable {S : Signature} {φ ψ : Formula S} {s x: Var} {k : Arity} {τ : Tuple k} {r : S k} {r₁ : S 1}

@[simp] theorem subst_bot : (bot : Formula S)[x↦s] = bot := rfl
@[simp] theorem subst_imp : (imp φ ψ)[x↦s] = imp (φ[x↦s]) (ψ[x↦s]) := rfl
@[simp] theorem subst_not : not φ[x↦s] = (not φ)[x↦s] := rfl
@[simp] theorem subst_and : (and φ ψ)[x↦s] = and φ[x↦s] ψ[x↦s] := rfl
@[simp] theorem subst_all : (all φ)[x↦s] = all (φ[x+1↦s+1]) := rfl
@[simp] theorem subst_rel : (rel r τ)[x↦s] = rel r (τ[x↦s]) := rfl

@[simp] theorem subst_rel0 : (rel r₁ ![0])[0↦s] = rel r₁ ![s] := by
  simp[Tuple.subst,Var.subst,subst,funext_iff]

@[simp] theorem subst_rel0' : (rel r₁) ![0][0↦s]  = rel r₁ ![s] := by
  simp[Tuple.subst,Var.subst,funext_iff]

end Formula

end

end FOL2
