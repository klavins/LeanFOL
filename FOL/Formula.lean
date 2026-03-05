--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import FOL.Var
import FOL.Tuple

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false

/-
Formulas
===
-/

abbrev Signature := Arity → Type

inductive Formula (S : Signature)
  | bot     : (Formula S)
  | rel {k} : S k → Tuple k  → (Formula S)
  | imp     : (Formula S) → (Formula S) → (Formula S)
  | all     : (Formula S) → (Formula S)

def Formula.not {S : Signature} (a : Formula S) : Formula S := (imp a bot)
def Formula.or {S : Signature} (a b : Formula S) : Formula S := (imp (not a) b)
def Formula.and {S : Signature} (a b : Formula S) : Formula S := not (or (not a) (not b))
def Formula.top {S : Signature} : Formula S := (not bot)
def Formula.ex {S : Signature} (a : Formula S) : Formula S := not (all (not a))

/-
Free Variables
===
-/

def Formula.free_vars {S : Signature} (φ : Formula S) : Finset ℕ :=
  match φ with
    | Formula.bot => {}
    | Formula.rel _ tuple => Finset.image tuple Finset.univ
    | Formula.imp ψ₁ ψ₂ => free_vars ψ₁ ∪ free_vars ψ₂
    | Formula.all ψ => ((free_vars ψ).filter (· ≠ 0)).image (· - 1)

/-
Substitution
===
-/

def Formula.subst {S : Signature} (t : Var) (x : Var) : Formula S → Formula S
  | bot => bot
  | rel r tuple => rel r (Tuple.subst t x tuple)
  | imp φ ψ => imp (subst t x φ) (subst t x ψ)
  | all φ => all (subst (t+1) (x+1) φ)

notation:max φ "[" x " ↦ " s "]" => Formula.subst s x φ

section

namespace Formula

variable {S : Signature} {φ ψ : Formula S} {s x : Var}
         {k : Arity} {τ : Tuple k} {r : S k} {r₁ : S 1}

@[simp] theorem subst_bot : (bot : Formula S)[x↦s] = bot := rfl

@[simp] theorem subst_imp : (imp φ ψ)[x↦s] = imp (φ[x↦s]) (ψ[x↦s]) := rfl

@[simp] theorem subst_not : not φ[x↦s] = (not φ)[x↦s] := rfl

@[simp] theorem subst_and : (and φ ψ)[x↦s] = and φ[x↦s] ψ[x↦s] := rfl

@[simp] theorem subst_all : (all φ)[x↦s] = all (φ[x+1↦s+1]) := rfl

@[simp] theorem subst_rel : (rel r τ)[x↦s] = rel r (τ[x↦s]) := rfl

@[simp] theorem subst_rel0 : (rel r₁ ![0])[0↦s] = rel r₁ ![s] := by
  simp[funext_iff]

@[simp] theorem subst_rel0' : (rel r₁) ![0][0↦s]  = rel r₁ ![s] := by
  simp[funext_iff]

end Formula

end

end FOL
