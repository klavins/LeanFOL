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

/-
Theorems about Formulas
===
-/

namespace Formula

variable {S : Signature} {φ ψ : Formula S} {f g : Renamer}
         {s x y t : Var} {level : Level}

@[simp] theorem lift_inst_at (t : Var) (level : Level):
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

@[simp] theorem inst_eq : φ.inst t = φ.inst_at t 0 := rfl

theorem inst_at_eq_rename : φ.inst_at t level = φ.rename (Var.inst_at t level) := by
  induction φ generalizing t level with
  | bot => rfl
  | rel r τ => simp[Formula.inst_at, Formula.rename, Tuple.inst_at]
  | imp g h ihg ihh => simp[Formula.inst_at, Formula.rename, ihg, ihh]
  | all g ih =>
    simp only [Formula.inst_at, Formula.rename]
    simp[lift_inst_at]
    exact ih

end Formula


/-
Theorems about Satisfies
===
-/

section

variable {α : Type u} {S : Signature} {Γ : Context S} {M : Model S α}
         {φ ψ : Formula S} {a : Assignment α} {x : α} {f : Renamer}
         {t : Var} {level : Level}

lemma update_comp_lift : update a x ∘ f.lift = update (a ∘ f) x := by
  funext j; cases j with
  | zero => simp [update, Renamer.lift]
  | succ n => simp [Function.comp, update, Renamer.lift]

lemma satisfies_rename : satisfies M a (φ.rename f) ↔ satisfies M (a ∘ f) φ := by
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

def inst_assign {α : Type u} (A : Assignment α) (t level : ℕ) : Assignment α :=
  fun j => if j < level then A j else if j = level then A t else A (j - 1)

theorem inst_assign_comp : a ∘ Var.inst_at t level = inst_assign a t level := by
  funext j; simp only [Function.comp, Var.inst_at, inst_assign]; split_ifs <;> rfl

theorem satisfies_inst_at :
    satisfies M a (φ.inst_at t level) ↔ satisfies M (inst_assign a t level) φ := by
  rw [Formula.inst_at_eq_rename, satisfies_rename, inst_assign_comp]

@[simp] theorem update_shift : update a x ∘ Var.shift 0 = a := by
  funext j
  simp [Function.comp, update, Var.shift]

end

/-
Soundness
===
-/

section

variable {α : Type u} {S : Signature} {Γ : Context S} {M : Model S α}
         {φ ψ : Formula S} {a : Assignment α} {x : α} {f : Renamer}
         {t : Var} {level : Level}

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

end

end FOL2
