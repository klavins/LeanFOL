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

/-
Soundness
===
-/

variable {S : Signature} {Γ : Context S} {φ ψ : Formula S} {t : Var}

theorem sound_ax (h : φ ∈ Γ) : Γ ⊨ φ := by
  intro α M a hψ
  exact hψ φ h

theorem sound_bot_elim (h : Γ ⊨ Formula.bot) : Γ ⊨ φ := by
  intro α M a hΓ
  exact absurd (h M a hΓ) (by simp [satisfies])

theorem sound_im_intro (h : Γ ∪ {φ} ⊨ ψ) : Γ ⊨ Formula.imp φ ψ := by
  intro α M a hΓ hφ
  exact h M a (fun ω hω => by
    cases hω with
    | inl h1 => exact hΓ ω h1
    | inr h1 => simp at h1; rw [h1]; exact hφ)

theorem sound_im_elim (h₁ : Γ ⊨ Formula.imp φ ψ) (h₂ : Γ ⊨ φ) : Γ ⊨ ψ := by
  intro α M a hΓ
  exact h₁ M a hΓ (h₂ M a hΓ)

theorem sound_all_intro (h : Formula.shift '' Γ ⊨ φ) : Γ ⊨ Formula.all φ := by
  intro α M a hΓ x
  exact h M (update a x) (fun χ hχ => by
    obtain ⟨ψ, hψ, rfl⟩ := hχ
    rw [show ψ.shift = ψ.rename (Var.shift 0) from rfl, satisfies_rename]
    exact hΓ ψ hψ)

theorem sound_all_elim (h : Γ ⊨ Formula.all φ) : Γ ⊨ φ.inst t := by
  intro α M a hψ
  rw [Formula.inst_eq, satisfies_inst_at]
  have : inst_assign a t 0 = update a (a t) :=
    funext fun j => by simp [inst_assign, update]
  rw [this]
  exact h M a hψ (a t)

open Formula in
theorem sound_em : Γ ⊨ Formula.or (Formula.not φ) φ:= by
  intro  α M a hψ h1
  unfold Formula.not at h1
  simp[satisfies] at h1
  exact h1

open Provable Formula in
theorem sound : Γ ⊢ φ → Γ ⊨ φ := by
  intro h
  induction h with
  | ax h                 => exact sound_ax h
  | bot_elim _ ih        => exact sound_bot_elim ih
  | im_intro _ ih        => exact sound_im_intro ih
  | im_elim _ _ ih₁ ih₂  => exact sound_im_elim ih₁ ih₂
  | all_intro _ ih       => exact sound_all_intro ih
  | all_elim _ ih        => exact sound_all_elim ih
  | em                   => exact sound_em

end FOL
