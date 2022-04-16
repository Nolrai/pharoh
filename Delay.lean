open Option
open Function

universe u v w

-- inductive FFree (p : Type u → Type v) (α : Type w) where
--   | Pure : α → FFree p α
--   | Impure {x : Type u} : p x → (x → FFree p α) → FFree p α

-- def FFree_map (f : α → β) : FFree p α → FFree p β
--   | FFree.Pure a => FFree.Pure (f a)
--   | FFree.Impure m cont => FFree.Impure m (λ x => FFree_map f (cont x))

-- lemma FFree_map_Impure : ∀ {β} (f : α → β) (m : p τ) (cont : τ → FFree p α), 
--   FFree_map f (FFree.Impure m cont) = FFree.Impure m (λ x => FFree_map f (cont x)) := 
--   λ _ _ _=> rfl

-- instance : Functor (FFree p) where
--   map := FFree_map

-- lemma FFree_id_map (p : Type → Type) {α : Type} (x : FFree p α) : 
--   id <$> x = x := by
--     have : ∀ α (y : FFree p α), id <$> y = FFree_map id y := λ _ _ => rfl
--     rw [this]
--     induction x with
--     | Pure a => rfl
--     | Impure m cont ih => 
--       rw [FFree_map_Impure]
--       simp
--       funext y
--       apply ih

-- lemma FFree_comp_map 
--   (p : Type → Type) {α β γ : Type} 
--   (g : α → β) (h : β → γ) (x : FFree p α) : (h ∘ g) <$> x = h <$> g <$> x := by
--   induction x with
--   | Pure x =>
--     have : ∀ {τ σ} (f : τ → σ) (y : τ), (f <$> FFree.Pure y : FFree p σ) = FFree.Pure (f y) := λ _ _ => rfl
--     rw [this, this, this]
--     simp
--   | Impure px cont ih => 
--     have : ∀ {τ σ} (f : τ → σ) (y : FFree p τ), f <$> y = FFree_map f y := λ _ _ => rfl 
--     rw [this, this, this]
--     rw [FFree_map_Impure, FFree_map_Impure, FFree_map_Impure]
--     simp
--     funext z
--     rw [← this, ← this, ← this]
--     apply ih

-- instance : LawfulFunctor (FFree p) where
--   map_const := rfl
--   id_map := FFree_id_map _
--   comp_map := FFree_comp_map _ 

-- inductive Until : Type u → Type (u + 1) where
--   | intro {σ τ : Type u} : (σ → σ ⊕ τ) → σ → Until τ

-- inductive Failure : Type u → Type (u + 1) where
--   | fail {τ : Type u} : Failure τ

-- def Eff : List (Type u → Type v) → Type u → Type v
--   | [], _ => PEmpty
--   | (x :: xs), τ => x τ ⊕ Eff xs τ

-- def runEmpty : FFree (Eff []) α → α
--   | FFree.Pure a => a
--   | FFree.Impure m cont => match m with .
