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

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false


/-
Renaming
===
-/

abbrev Renamer := Var → Var

def Renamer.lift (f : Renamer) : Renamer
  | 0 => 0
  | n+1 => (f n) + 1

@[simp] theorem Renamer.lift_id : lift id = id := by
  funext i
  simp[lift]
  cases i <;> rfl

@[simp] theorem Renamer.lift_comp {f g : Renamer}
  : lift (g ∘ f) = lift g ∘ lift f := by
  funext i
  simp[lift]
  cases i <;> rfl

@[simp] theorem Renamer.lift_shift {f : Renamer}
  : lift f ∘ Var.shift 0 = Var.shift 0 ∘ f := by
  funext i
  simp[lift]
  rfl

@[simp] theorem hlift {level : Level} : Renamer.lift (Var.shift level) = Var.shift (level + 1) := by
    funext v
    cases v
    · simp [Renamer.lift, Var.shift]
    · simp only [Renamer.lift, Var.shift, Nat.succ_lt_succ_iff]
      split_ifs <;> rfl

def Formula.rename {S : Signature} (φ : Formula S) (f : Renamer) : Formula S :=
  match φ with
    | bot => bot
    | rel r t => rel r (f ∘ t)
    | imp ψ₁ ψ₂ => imp (rename ψ₁ f) (rename ψ₂ f)
    | all ψ => all (rename ψ (f.lift))

section
open Formula

variable {S : Signature} {φ : Formula S} {f g : Renamer}

@[simp] theorem rename_id : φ.rename id = φ := by
  induction φ with
  | bot => rfl
  | rel r t => simp [rename]
  | imp ψ₁ ψ₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]
  | all ψ ih => simp [rename, ih]

@[simp] theorem rename_comp : (φ.rename f).rename g = φ.rename (g ∘ f) := by
  induction φ generalizing f g with
  | bot => rfl
  | rel r t => simp [rename, Function.comp_assoc]
  | imp ψ₁ ψ₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]
  | all ψ ih => simp [rename, ih]

@[simp] theorem lift_inst_at (t : Var) (level : Level) :
    Renamer.lift (Var.inst_at t level) = Var.inst_at (t+1) (level+1) := by
  funext v
  cases v with
  | zero => simp [Renamer.lift, Var.inst_at]
  | succ n =>
     simp[Renamer.lift, Var.inst_at]
     split_ifs
     · simp
     · simp
     · apply Nat.succ_pred_eq_of_ne_zero
       aesop

end

/-
Shifting
===
-/

def Formula.shift {S : Signature} (φ : Formula S) := φ.rename (Var.shift 0)

end FOL
