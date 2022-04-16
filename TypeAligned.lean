import Mathlib.Data.List.Basic

namespace TypeAligned

inductive List (arr : Type → Type → Type) : Type → Type → Type 2 where
  | nil : List arr α α 
  | cons : arr α β → List arr β γ → List arr α γ

open List

instance (arr) (α : Type) : EmptyCollection (List arr α α) where
  emptyCollection := nil
  
notation "[]" => List.nil
infixr:50 "∷" => List.cons 

inductive Deque (arr : Type → Type → Type) (α γ : Type) : Type 2 where 
  | mk (β : Type) : List arr α β → List (flip arr) γ β → Deque arr α γ

open Deque

instance (arr) (α : Type) : EmptyCollection (Deque arr α α) where
  emptyCollection := Deque.mk α nil nil

def pushUnder (x : arr α β) : Deque arr β γ → Deque arr α γ
  | mk γ' back front => mk γ' (x ∷ back) front

def popTop
  (deque : Deque arr α γ) :
  (Σ β, arr β γ × Deque arr α β) ⊕' (α = γ ∧ HEq deque (∅ : Deque arr α α)) :=
  match deque with
  | mk _ [] [] => PSum.inr (refl, refl)
  | mk γ' back (x ∷ front) => PSum.inl ((_, x), mk γ' back front)