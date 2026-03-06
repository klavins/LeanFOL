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
import FOL.V1.Entailment

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false


namespace Examples

inductive Graph : Signature
  | E   : Graph 2
  deriving Repr

inductive Plain : Signature
  | P : Plain 1
  | Q : Plain 1
  deriving Repr

open Plain in
def MP : Model Plain ℕ := {
  interp := fun sym f => match sym with
    | P => Even (f 0)
    | Q => Odd (f 0)
}

open Formula Plain

def f0 : Formula Plain := (imp (rel P ![0]) (rel Q ![0]))

def f1 : Formula Plain :=
  imp (all (rel P ![0]))
      (imp (all (imp (rel P ![0]) (rel Q ![0])))
           (all (rel Q ![0])))

example : free_vars f0 = {0} := rfl

example : free_vars f1 = ∅ := rfl

example : f0[0↦3] = (imp (rel P ![3]) (rel Q ![3])) := by simp[f0]

example : f1[0↦3] = f1 := by simp[f1,funext_iff]

/- `∀ x, P(x) → Q(x)` applied to `10` is `P(10) → Q(10)` -/
example : inst 10 f0 = subst 10 0 f0 := by simp[f0,funext_iff]

/- `bot` is a fixed point. So, for example,
   `∀ x, False applied to 5` is `False` -/
example : inst 5 (bot (S := Plain)) = bot := by simp

/- The index `0` (the bound var) gets substituted. So for example,
  `∀ x, P(x)` applied to `5` is `P(5)` -/
example : inst 5 (rel P ![0]) = rel P ![5] := by simp[funext_iff]

/- index `1` (a free var above `level`) gets decremented to `0` so it still refers to the same thing.
   So for example,
   `∀ x, P(y)` applied to `5` is `P(y)`
-/
example : inst 5 (rel P ![1]) = rel P ![0] := by simp[funext_iff]

/- A mixed example.
  `∀ x, P(x) → Q(y)` applied to `5` is `P(5) → Q(y)` -/
example : inst 5 (imp (rel P ![0]) (rel Q ![1])) =
          imp (rel P ![5]) (rel Q ![0]) := by simp[funext_iff]

/- Inst leaves inner binders alone. For example,
  `∀ x, ∀ y, P(y)` applied to `5` gives `∀ x, P(x)`  -/
example : inst 5 (all (rel P ![0])) = all (rel P ![0]) := by simp[funext_iff]

/- Going under a binder shifts the substituted term. For example,
  `∀ x, ∀ y, P(y) → Q(x)` applied to `5` gives `∀ x, P(x) → Q(6)`
  which makes sense because in this case `x₆` in the sub-expression refers to global
  variable `x₅`.  -/
example : inst 5 (all (imp (rel P ![0]) (rel Q ![1]))) =
          all (imp (rel P ![0]) (rel Q ![6])) := by simp[funext_iff]

open Provable in
example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (all (rel P ![0])) := by
  apply im_intro
  simp
  apply ax
  simp

/- ⊢ ∀x, P(x) → P(x) — tests all_intro -/
open Provable in
example : ∅ ⊢ all (imp (rel P ![0]) (rel P ![0])) := by
  apply all_intro
  apply im_intro
  apply ax
  simp

/- P(y) ⊢ ∀x, P(x) → P(y) — tests that context is correctly shifted -/
open Provable in
example : {rel P ![0]} ⊢ all (imp (rel P ![0]) (rel P ![1])) := by
  apply all_intro
  apply im_intro
  apply ax
  apply Set.mem_union_left
  simp
  congr
  simp[funext_iff,Var.shift]

/- ∀x, P(x) ⊢ P(5) — tests all_elim -/
open Provable in
example : {all (rel P ![0])} ⊢ rel P ![5] := by
  have : rel P ![5] = (rel P ![0]).inst 5 := by
    simp[Tuple.inst_at,funext_iff]
  rw[this]
  apply all_elim
  apply ax
  simp

/- ∀x, P(x) ⊢ P(y) — all_elim at t=0: bound var index equals free var index -/
open Provable in
example : {all (rel P ![0])} ⊢ rel P ![0] := by
  have : rel P ![0] = (rel P ![0]).inst 0 := by
    simp[Tuple.inst_at,funext_iff]
  conv => rhs; rw[this]
  apply all_elim
  apply ax
  simp

/- P(y) ⊢ ∀x, P(y) — all_intro where bound variable doesn't appear in body -/
open Provable in
example : {rel P ![0]} ⊢ all (rel P ![1]) := by
  apply all_intro
  apply ax
  simp
  congr
  simp[Var.shift,funext_iff]

/- ∀x, ∀y, P(y) ⊢ P(3) — nested all_elim: tests level increment inside all_elim -/
open Provable in
example : {all (all (rel P ![0]))} ⊢ rel P ![3] := by
  have : rel P ![3] = (rel P ![0]).inst 3 := by
    simp[Tuple.inst_at,funext_iff]
  rw[this]
  apply all_elim
  have : (rel P ![0]).all = ((rel P ![0]).all).inst 0 := by
    simp[Tuple.inst_at,funext_iff]
  rw[this]
  apply all_elim
  apply ax
  simp[funext_iff]

example {S : Signature} {P Q : S 1}
  : ∅ ⊨ imp (all (rel P ![0]))
            (imp (all (imp (rel P ![0]) (rel Q ![0])))
                 (all (rel Q ![0]))) := by
  intro α M a h
  simp only[satisfies]
  intro h1 h2 x
  exact h2 x (h1 x)

end Examples

end FOL
