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
import FOL.V1.Instantiation
import FOL.V1.Provable

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false

/-
Models
===
-/

universe u

def Assignment (α : Type u) := ℕ → α

def update {α : Type u} (A : Assignment α) (v : α) :=
  fun j => if j=0 then v else A (j-1)

def update_at {α : Type u} (x : ℕ) (v : α) (A : Assignment α) :=
  fun j => if j=x then v else A j

def inst_assign {α : Type u} (A : Assignment α) (t level : ℕ) : Assignment α :=
  fun j => if j < level then A j else if j = level then A t else A (j - 1)

structure Model (S : Signature) (α : Type u) where
  interp {arity} : S arity → (Fin arity → α) → Prop

open Formula in
def satisfies {S : Signature} {α : Type u}
  (M : Model S α) (A : Assignment α) (f : Formula S) : Prop :=
  match f with
    | bot => false
    | rel r t => M.interp r (A ∘ t)
    | imp g h => satisfies M A g → satisfies M A h
    | all g  => ∀ x : α, satisfies M (update A x) g

def models {S : Signature} {α : Type u} (M : Model S α) (f : Formula S) :=
  ∀ a, satisfies M a f

abbrev entails {S : Signature} (Γ : Context S) (φ : Formula S) : Prop :=
 ∀ {β : Type} (M : Model S β) (a : Assignment β), (∀ ψ ∈ Γ, satisfies M a ψ) → satisfies M a φ

infix:25 " ⊨ " => entails

/-
Theorems about Satisfies
===
-/

variable {α : Type u} {S : Signature} {Γ : Context S} {M : Model S α}
         {φ ψ : Formula S} {a : Assignment α} {x : α} {f : Renamer}
         {t : Var} {level : Level}

lemma update_comp_lift : update a x ∘ f.lift = update (a ∘ f) x := by
  funext j; cases j with
  | zero => simp [update, Renamer.lift]
  | succ n => simp [Function.comp, update, Renamer.lift]

lemma satisfies_rename
  : satisfies M a (φ.rename f) ↔ satisfies M (a ∘ f) φ := by
  induction φ generalizing a f with
  | bot => simp [satisfies, Formula.rename]
  | rel r t => simp [satisfies, Function.comp_assoc, Formula.rename]
  | imp g h ihg ihh => simp [satisfies, ihg, ihh, Formula.rename]
  | all g ih =>
    simp only [satisfies, Formula.rename]
    constructor <;> intro h x
    · have := (@ih (update a x) f.lift).mp (h x); rwa [update_comp_lift] at this
    · apply (@ih (update a x) f.lift).mpr
      rw [update_comp_lift]
      exact h x

theorem inst_assign_comp
  : a ∘ Var.inst_at t level = inst_assign a t level := by
  funext j
  simp only [Function.comp, Var.inst_at, inst_assign]
  split_ifs <;> rfl

theorem satisfies_inst_at :
    satisfies M a (φ.inst_at t level) ↔
    satisfies M (inst_assign a t level) φ := by
  rw [Formula.inst_at_eq_rename, satisfies_rename, inst_assign_comp]

@[simp] theorem update_shift : update a x ∘ Var.shift 0 = a := by
  funext j
  simp [Function.comp, update, Var.shift]

end FOL
