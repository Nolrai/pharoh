import Mathlib

inductive Ty where
  | N : Ty
  | arr : Ty → Ty → Ty

open Ty

infix:50 "⇒" => Ty.arr 

def el : Ty → Type
  | N => ℕ
  | τ ⇒ σ => el τ → el σ 

section

variable (lits : List Ty)

inductive STLC : List Ty → Ty → Type where
  | Lit {n} : STLC ctx (lits.get n)
  | Here {ctx τ} : STLC (τ :: ctx) τ
  | Shift {ctx τ σ} : STLC ctx τ → STLC (σ :: ctx) τ
  | App {ctx τ σ} : STLC ctx (σ ⇒ τ) → STLC ctx σ → STLC ctx τ
  | Abs {ctx τ σ} : STLC (σ :: ctx) τ → STLC ctx (σ ⇒ τ)

inductive TyList : List Ty → Type where
  | nil : TyList []
  | cons {τ ctx} : el τ → TyList ctx → TyList (τ :: ctx)

  