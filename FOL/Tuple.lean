--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import FOL.Var

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false

/-
Tuples
===
-/

abbrev Tuple (k : Arity) := Fin k → Var

def Tuple.shift {k} (level : Level) (tuple : Tuple k) : Tuple k :=
  (Var.shift level) ∘ tuple

def Tuple.unshift {k} (level : Level) (tuple : Tuple k) : Tuple k :=
  (Var.unshift level) ∘ tuple

def Tuple.inst_at {k} (level : Level) (t : Var) (tuple : Tuple k) : Tuple k :=
  (Var.inst_at t level) ∘ tuple

def Tuple.subst {k} (s x : Var) (tuple : Tuple k) : Tuple k :=
  (Var.subst s x) ∘ tuple

notation:max t "[" x " ↦ " s "]" => Tuple.subst s x t


/-
Theorems About Tuples
===
-/


section

namespace Tuple

variable {k : Arity} {level : Level} {s t x y : Var} {τ : Tuple k} {i : Fin k}

@[simp]
theorem unshift_shift : (unshift (k := k) level) ∘ (shift (k := k) level) = id := by
  funext tuple
  simp[unshift,shift,←Function.comp_assoc]

@[simp]
theorem subst_apply : τ[x↦s] i = (if τ i = x then s else τ i) := rfl

@[simp]
theorem inst_at_apply : inst_at level t τ i = Var.inst_at t level (τ i) := rfl

@[simp]
theorem inst_at_shift : inst_at level t (shift level τ) = τ := by
  funext i; simp [shift, Var.inst_at_shift]

@[simp]
theorem inst_at_subst (hs : level ≤ s) (hx : level ≤ x) :
  (inst_at level t τ)[x↦s] = (τ[x+1↦s+1]).inst_at level (t[x↦s]) := by
  funext i
  simp only [Tuple.subst, Tuple.inst_at, Function.comp]
  exact Var.subst_inst_at hs hx

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x) : τ[x↦s][y↦t] = τ[y↦t][x↦s[y↦t]] := by
  simp[subst,h₁,h₂,funext_iff]

@[simp] theorem subst_id : τ[x↦x] = τ := by
  simp[subst,funext_iff,Var.subst]
  intro _ hi
  exact Eq.symm hi


end Tuple
end
end FOL
