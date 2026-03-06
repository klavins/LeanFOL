--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace FOL2

/-!
# FOL Definitions
-/

universe u

abbrev Var := ℕ
abbrev Arity := ℕ
abbrev Level := ℕ

abbrev Tuple (k : Arity) := Fin k → Var

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

abbrev Renamer := Var → Var

def Renamer.lift (f : Renamer) : Renamer
  | 0 => 0
  | n+1 => (f n) + 1

def Formula.rename {S : Signature} (φ : Formula S) (f : Renamer) : Formula S :=
  match φ with
    | bot => bot
    | rel r t => rel r (f ∘ t)
    | imp ψ₁ ψ₂ => imp (rename ψ₁ f) (rename ψ₂ f)
    | all ψ => all (rename ψ (f.lift))

def Var.shift (level : Level) (v : Var) : Var :=
  if v < level then v else v + 1

def Formula.shift {S : Signature} (φ : Formula S) := φ.rename (Var.shift 0)

def Var.inst_at (t : Var) (level : Level) (v : Var) : Var :=
  if v < level then v
  else if v = level then t
  else v - 1

def Tuple.inst_at {k} (level : Level) (t : Var) (tuple : Tuple k) : Tuple k :=
  (Var.inst_at t level) ∘ tuple

def Formula.inst_at {S : Signature} (t : Var) (level : Level) : Formula S → Formula S
  | Formula.bot         => Formula.bot
  | Formula.rel r tuple => Formula.rel r (tuple.inst_at level t)
  | Formula.imp φ ψ     => Formula.imp (inst_at t level φ) (inst_at t level ψ)
  | Formula.all φ       => Formula.all (inst_at (t+1) (level+1) φ)

def Formula.inst {S : Signature} (t : Var) : Formula S → Formula S := inst_at t 0

abbrev Context S := Set (Formula S)

open Formula in
inductive Provable {S : Signature} : Context S → Formula S → Prop
  | ax {Γ φ}              : (h : φ ∈ Γ) → Provable Γ φ
  | bot_elim {Γ φ}        : Provable Γ bot → Provable Γ φ
  | im_intro {Γ φ ψ}      : Provable (Γ ∪ {φ}) ψ → Provable Γ (imp φ ψ)
  | im_elim {Γ φ ψ}       : Provable Γ (imp φ ψ) → Provable Γ φ → Provable Γ ψ
  | all_intro {Γ φ}       : Provable (shift '' Γ) φ → Provable Γ (all φ)
  | all_elim {Γ φ t}      : Provable Γ (all φ) → Provable Γ (inst t φ)
  | em {Γ φ}              : Provable Γ (or (not φ) φ)

infix:50 " ⊢ " => Provable

def Assignment (α : Type u) := ℕ → α

def update {α : Type u} (A : Assignment α) (v : α) :=
  fun j => if j=0 then v else A (j-1)

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

end FOL2
