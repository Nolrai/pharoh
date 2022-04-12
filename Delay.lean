import Mathlib.Data.Nat.Basic

#print OptionT
#print StateT

open Option

def delay (n' : Option (α × ℕ)) : StateT ℕ OptionM α :=
  match n' with
  | none => failure
  | some (a, n) => 
    λ k =>
      if n ≤ k
        then some (a, n - k)
        else none

def delay_some_le {α} (a : α) (h : n ≤ k) : 
  delay (some (a, n)) k = some (a, k - n) := by
  have : delay (some (a, n)) = 
    λ k =>
      if n ≤ k
        then some (a, n - k)
        else none
     := rfl
  rw [this]
  simp
  rw [if_pos h]

def delay_some_gt {α} (a : α) (h : n > k) : 
  delay (some (a, n)) k = none := by
  have : delay (some (a, n)) = 
    λ k =>
      if n ≤ k
        then some (a, n - k)
        else none
     := rfl
  rw [this]
  simp
  rw [if_neg]
  rw [Nat.not_le]
  apply h

lemma delay_none {γ} : delay (none  : Option (γ × ℕ)) = failure := funext (λ x => rfl)

def Delay α := { x : StateT ℕ OptionM α // ∃ y, x = delay y}

def map_bind (M : Type → Type) [Monad M] (m : M α) (f' : α → M β) (f : β → γ) : 
  Functor.map f (bind m f') = bind m (Functor.map f ∘ f') := sorry

def map_pure (M : Type → Type) [Applicative M] (a : α) (f : α → β) : 
  Functor.map f (pure a : M α) = pure (f a) := sorry

def map_failure (M : Type → Type) [Alternative M] (f : α → β) : 
  Functor.map f (failure : M α) = failure := sorry

def map_delay_some {f : α → β} {a : α} : f <$> delay (some (a, n)) = delay (some (f a, n)) := sorry

def map_delay_none {f : α → β} : f <$> delay none = delay none := by
  ext
  intros n
  have : ∀ σ : Type, delay (none : Option (σ × ℕ)) = failure := λ σ => rfl
  rw [this, this, map_failure]

def Delay.map (f : α → β) : Delay α → Delay β
  | ⟨v, p⟩ => ⟨f <$> v, 
    match p with
    | ⟨some (a, n), h⟩ => ⟨some (f a, n), by
      simp
      rw [h, map_delay_some]
    ⟩
    | ⟨none, h⟩ => ⟨none, by 
      rw [h]
      apply map_delay_none
    ⟩ 
  ⟩

instance : Functor Delay := {
  map := Delay.map
}

def Delay.pure (a : α) : Delay α := ⟨delay (some (a, 0)), ⟨some (a, 0), rfl⟩⟩

lemma failure_bind {M : Type → Type} [Alternative M] [Monad M] (m : β → M α) : (failure >>= m) = failure :=
  sorry

lemma delay_bind {f : α → Delay β} : ∀ {x}, ∃ y, delay x >>= (Subtype.val ∘ f) = delay y
  | none => by
    exists (none : Option (β × ℕ))
    rw [delay_none, delay_none, failure_bind]
  | some (a, n) => 
    match (f a).property with
    | ⟨none, h⟩ => by 
      exists (none : Option (β × ℕ))
      
      
    

def Delay.bind (d : Delay α) (f : α → Delay β) : Delay β :=
  ⟨(d.val >>= (Subtype.val ∘ f)), sorry
  ⟩ 

instance : Monad Delay := {
  pure := Delay.pure
  bind := Delay.bind
}



