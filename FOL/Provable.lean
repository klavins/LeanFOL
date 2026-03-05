--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import FOL.Var
import FOL.Tuple
import FOL.Formula
import FOL.Rename
import FOL.Instantiation

namespace FOL

set_option linter.style.setOption false
set_option linter.flexible false

/-
Provability
===
-/

abbrev Context S := Set (Formula S)

def free_vars_context {S : Signature} (C : Context S) : Set Var :=
  ⋃ f ∈ C, f.free_vars

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

end FOL
