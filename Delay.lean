import Mathlib.Data.Nat.Basic

#print OptionT
#print StateT

open Option

def delay (n' : Option (α × ℕ)) : StateT ℕ OptionM α :=
  match n' with
  | none => failure
  | some (a, n) => do
    let k <- get
    guard (n ≤ k)
    set (k - n)
    pure a

def delay_some {α} (a : α) : 
  delay (some (a, n)) = (do
    let k <- get
    guard (n ≤ k)
    set (k - n)
    pure a
    )
  := rfl

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

def Delay.bind (d : Delay α) (f : α → Delay β) : Delay β :=
  ⟨(d.val.bind (Subtype.val ∘ f)), by 
    let ⟨w, h⟩ := d.property
    rw [h]
    clear h
    cases w with 
    | some y =>
      have H : ∀ {s m} (x : StateT s m α) (f : α → StateT s m β) [Monad m], StateT.bind x f = fun s => do {let (a, s) ← x s; f a s} := λ x f => rfl
      rw [H]; clear H
      simp
       
    | none => _
  ⟩ 

instance : Monad Delay := {
  pure := Delay.pure
  bind := Delay.bind
}



