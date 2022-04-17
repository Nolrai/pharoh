import Mathlib.Data.List.Basic

namespace TypeAligned

inductive List (arr : Type → Type → Type) : Type → Type → Type 2 where
  | nil : List arr α α 
  | cons : ∀ β, arr α β → List arr β γ → List arr α γ

notation "[]" => List.nil
infixr:60 "∷" => List.cons _

open List

instance (arr) (α : Type) : EmptyCollection (List arr α α) where
  emptyCollection := nil

lemma empty_def (arr α) : (∅ : List arr α α) = [] := rfl

instance (arr) (α : Type) : EmptyCollection (List (flip arr) α α) where
  emptyCollection := nil

lemma empty_def' (arr α) : (∅ : List (flip arr) α α) = [] := rfl

def hAppend {α β γ} (l : List arr α β) ( r : List arr β γ) : List arr α γ :=
  match l with
  | nil => r
  | cons γ' l ls => l ∷ hAppend ls r

instance : HAppend (List arr α β) (List arr β γ) (List arr α γ) where
  hAppend := hAppend

lemma nilAppend : ([] : List arr α α) ++ (x : List arr α β) = x := rfl
lemma consAppend {α β β' γ} (r : List arr β γ) (x : arr α β') (xs : List arr β' β) : 
  (cons β' x xs : List arr α β) ++ r = cons β' x (xs ++ r) := rfl

lemma Iff.bothTrue : P → Q → (P ↔ Q) := 
  λ p q => 
    { mp  := fun h => q
    , mpr := fun h => p 
    }

lemma Iff.bothFalse : ¬ P → ¬ Q → (P ↔ Q) := 
  λ p q => 
    { mp  := fun h => False.elim (p h)
    , mpr := fun h => False.elim (q h) 
    }

lemma HEq.first {α β} {a : α} {b : β} : HEq a b → α = β
  | HEq.refl _ => rfl

lemma HEq.snd {a : α} {b : α} : HEq a b -> a = b
  | HEq.refl _ => rfl

lemma ConsNotHEqNil_aux : ¬ HEq (cons α' l ls : List arr α α) ([] : List arr α α) := by
  simp

lemma ConsNotHEqNil_aux2 : HEq (cons α' l ls : List arr α β) (x : List arr α α) → 
  HEq (cons α' l ls : List arr α α) (x : List arr α α)
  | HEq.refl _ => HEq.refl _

lemma nilEqhAppend (α β) : ∀ (l : List arr α β) ( r : List arr β α), 
  ∅ = (l ++ r) ↔ (α = β ∧ HEq l r ∧ HEq r (nil : List arr α α))
  | nil, nil => by 
    apply Iff.bothTrue (Eq.trans (rfl : ∅ = []) rfl)
    repeat constructor
  | nil, cons β' r rs => by
    apply Iff.bothFalse
    rw [nilAppend]
    intros h
    cases h
    simp
  | cons α' l ls, r => by
    apply Iff.bothFalse
    
    rw [consAppend, empty_def]
    intros h
    cases h
    
    intros h
    cases h with | intro αβ right => 
    cases right with | intro lr rNil => 
    have : HEq (cons α' l ls) ([] : List arr α α) := by
      have test := HEq.first rNil
      apply HEq.trans lr rNil
    simp


def reverseSpec : List arr α β → List (flip arr) β α
  | nil => nil
  | cons γ x xs => reverseSpec xs ++ (cons _ (x : flip arr γ α) nil : List (flip arr) _ _)

def reverseEmpty (a : List arr α α) : reverseSpec a = ∅ ↔ (a = ∅) := 
  Iff.intro 
    ( λ h => by 
      cases a with
      | nil => rfl
      | cons β x xs => 
        have : reverseSpec (cons β x xs) = reverseSpec xs ++ (cons _ (x : flip arr β α) nil : List (flip arr) _ _)
          := rfl
        rw [this] at h
    ) 
    _

inductive Queue (arr : Type → Type → Type) (α γ : Type) : Type 2 where 
  | mk (β : Type) : List arr α β → List (flip arr) γ β → Queue arr α γ

open Queue

instance (arr) (α : Type) : EmptyCollection (Queue arr α α) where
  emptyCollection := Queue.mk α nil nil

def enqueue (x : arr α β) : Queue arr β γ → Queue arr α γ
  | mk γ' back front => mk γ' (x ∷ back) front

def dequeue :
  ∀ (deque : Queue arr α γ),
  (Σ β, Queue arr α β × arr β γ ) ⊕' (α = γ ∧ HEq deque (∅ : Queue arr α α)) := by
  intros deque
  cases deque with
  | mk γ' back front =>
    cases front with
    | nil =>
      cases reverseSpec back with
      | nil =>
        apply PSum.inr
        simp
        


    | cons _ front middle =>
      apply PSum.inl
      exact (Sigma.mk _ (mk γ' back middle, front))

