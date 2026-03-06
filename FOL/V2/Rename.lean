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
# Theorems about Renaming
-/

@[simp] theorem Renamer.lift_id : lift id = id := by
  funext i
  simp[lift]
  cases i <;> rfl

@[simp] theorem Renamer.lift_comp {f g : Renamer} : lift (g ∘ f) = lift g ∘ lift f := by
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

open Formula
variable {S : Signature} {φ : Formula S}

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

end FOL2
