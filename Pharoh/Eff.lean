import Mathlib

import Pharoh.Down

open Option
open Function
open Std
open Nat

universe u v w

def In' (a:α) (l : List α) : Type := {n // l.get? n = some a} 

infix:50 " ∈' " => In'

inductive Freer (r : List (Type u → Type v)) (α : Type u) where
  | MkPure : α → Freer r α
  | MkImpure (f : Type u → Type v) : f ∈' r → f α → (α → Freer r α) → Freer r α


open Freer

def Freer.run_empty : Freer ∅ α → α
  | MkPure a => a

inductive Fix : Type u → Type (u + 2) where
  | Until (α β : Type u) : Fix ((α → α ⊕ β) → β)

def Freer.run_fix_aux : ℕ → ∀ {α}, Freer (Fix :: l) α → Option (Freer l α)
  | 0, _, _ => none
  | n+1, α, m =>
    match m with
      | MkPure a => some (MkPure a)
      | MkImpure f ⟨0, p⟩ fa c => 
        by 
        simp at p 
        have fa' : Fix α := by rw [p]; assumption
        cases fa' with | Until α β =>

      | MkImpure f inR fa c => _
     

def Freer.run_fix : Freer (Fix :: l) α → ℕ → Option (Freer l α) := 
  λ m n => Freer.run_fix_aux n m