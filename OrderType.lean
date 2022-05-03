import Mathlib.Init.Algebra.Order

universe u

inductive Squash' (α : Type u) : Prop
  | intro : α → Squash' α

class WellOrder (α : Type u) extends LinearOrder α where
  getMin : (∀ Q, Decidable Q) → ∀ (P : α → Prop) a, P a → ∃ b, P b ∧ ∀ c, P c → b ≤ c

structure Box  where
  carrier : Type u
  order : WellOrder carrier

namespace Box

instance : CoeSort Box (Type u) where
  coe := Box.carrier

instance (b : Box) : WellOrder b := b.order 

structure equiv (a b : Box) where
  f : a → b
  g : b → a
  f_mono : ∀ x y : a, x ≤ y → f x ≤ f y
  g_mono : ∀ x y : b, x ≤ y → g x ≤ g y
  f_of_g : ∀ x, f (g x) = x
  g_of_f : ∀ x, g (f x) = x

lemma equiv_refl : equiv a a where
  f := id
  g := id
  f_mono := λ _ _ => id
  g_mono := λ _ _ => id
  f_of_g := λ _ => rfl
  g_of_f := λ _ => rfl

lemma equiv_symm : equiv a b → equiv b a
  | ab => {
    f := ab.g
    g := ab.f
    f_mono := ab.g_mono
    g_mono := ab.f_mono
    f_of_g := ab.g_of_f
    g_of_f := ab.f_of_g
  }

lemma equiv_trans : equiv a b → equiv b c → equiv a c
  | ab, bc => {
    f := bc.f ∘ ab.f
    g := ab.g ∘ bc.g
    f_mono := λ x y h => by 
      simp
      apply bc.f_mono
      apply ab.f_mono
      exact h
    g_mono := λ x y h => by 
      simp
      apply ab.g_mono
      apply bc.g_mono
      exact h
    f_of_g := λ x => by simp; rw [ab.f_of_g, bc.f_of_g]
    g_of_f := λ x => by simp; rw [bc.g_of_f, ab.g_of_f]
  }

def OrderSetoid : Setoid Box where
  r := λ a b => Squash' (equiv a b)
  iseqv := { 
    refl := fun x => Squash'.intro equiv_refl,
    symm := fun {x y} xy =>
      match xy with
      | Squash'.intro xy => Squash'.intro (equiv_symm xy),
    trans := fun {x y z} xy yz =>
      match xy, yz with
      | Squash'.intro xy, Squash'.intro yz => Squash'.intro (equiv_trans xy yz)
  }

def Ordinal := Quotient OrderSetoid

def Ordinal.mk := Quotient.mk OrderSetoid

namespace Ordinal

instance empty_WellOrder : WellOrder Empty where
  le := by intros a; cases a
  le_refl := by intros a; cases a
  le_trans := by intros a; cases a
  le_antisymm := by intros a; cases a
  lt := by intros a; cases a
  lt_iff_le_not_le := by intros a; cases a
  le_total := by intros a; cases a
  decidable_le := by intros a; cases a
  getMin := by intros _ _ a; cases a

instance : OfNat Ordinal 0 where
  ofNat := Ordinal.mk ⟨Empty, empty_WellOrder⟩

instance unit_WellOrder : WellOrder Unit where
  le := λ _ _ => True
  le_refl := λ _ => True.intro
  le_trans := λ _ _ _ _ _ => True.intro
  le_antisymm := λ () () => by intros _ _; rfl
  lt := λ _ _ => False
  lt_iff_le_not_le := λ () () => {mp := λ p => p.elim, mpr := λ ⟨xy, yx⟩ => (yx xy).elim}
  le_total := λ _ _ => Or.inl True.intro
  decidable_le := λ _ _ => isTrue True.intro
  getMin := λ LEM P a Pa => 
    match a with
    | () => ⟨(), Pa, λ c Pc => True.intro⟩

instance : OfNat Ordinal 1 where
  ofNat := Ordinal.mk ⟨Unit, unit_WellOrder⟩

section Sum_1

variable {α β : Type u} [poa : PartialOrder α] [pob : PartialOrder β]

open Sum

inductive Sum.le : α ⊕ β → α ⊕ β → Prop
  | inl {x y : α} : x ≤ y → le (inl x) (inl y)
  | inr {x y : β} : x ≤ y → le (inr x) (inr y)
  | inl_inr {x : α} {y : β} : le (inl x) (inr y)

inductive Sum.lt : α ⊕ β → α ⊕ β → Prop
  | inl {x y : α} : x < y → lt (inl x) (inl y)
  | inr {x y : β} : x < y → lt (inr x) (inr y)
  | inl_inr {x : α} {y : β} : lt (inl x) (inr y)

open Sum

lemma  le_refl : ∀ x : α ⊕ β, Sum.le x x := λ x => 
  match x with
  | Sum.inl x => le.inl (poa.le_refl x)
  | Sum.inr x => le.inr (pob.le_refl x)

lemma le_trans : ∀ (x y z : α ⊕ β), Sum.le x y → Sum.le y z → Sum.le x z
  | inl x, inl y, inl z, le.inl xy, le.inl yz => le.inl (poa.le_trans x y z xy yz)
  | inr x, inr y, inr z, le.inr xy, le.inr yz => le.inr (pob.le_trans x y z xy yz)
  | inl x, _, inr z, _, _ => le.inl_inr

lemma lt_iff_le_not_le (x y : α ⊕ β) : lt x y ↔ (le x y ∧ ¬ le y x) where
  mp := λ x_lt_y => 
    match x_lt_y with
    | lt.inl x_lt_y => 
      have ⟨xy, nyx⟩ := lt_iff_le_not_le.mp x_lt_y
      ⟨ le.inl xy 
      , λ h =>
        match h with
        | le.inl h => nyx h 
      ⟩ 
    | lt.inr x_lt_y => have ⟨xy, nyx⟩ := lt_iff_le_not_le.mp x_lt_y
      ⟨ le.inr xy 
      , λ h =>
        match h with
        | le.inr h => nyx h 
      ⟩
    | lt.inl_inr => ⟨le.inl_inr, λ h => by cases h⟩
  mpr := λ ⟨ xy, nxy ⟩ => 
    match xy with
    | le.inl xy => lt.inl $ (poa.lt_iff_le_not_le _ _).mpr ⟨xy, λ yx => nxy (le.inl yx) ⟩ 
    | le.inr xy => lt.inr $ (pob.lt_iff_le_not_le _ _).mpr ⟨xy, λ yx => nxy (le.inr yx) ⟩
    | le.inl_inr => lt.inl_inr

instance Sum.Preorder : Preorder (α ⊕ β) where
  le := Sum.le
  le_refl := le_refl
  le_trans := le_trans
  lt := Sum.lt
  lt_iff_le_not_le := lt_iff_le_not_le

end Sum_1

open Sum

namespace Sum

lemma le_antisymm [woa : PartialOrder α] [wob : PartialOrder β] (x y : α ⊕ β) : x ≤ y → y ≤ x → x = y
  | le.inl xy, le.inl yx => congr_arg Sum.inl $ woa.le_antisymm _ _ xy yx
  | le.inr xy, le.inr yx => congr_arg Sum.inr $ wob.le_antisymm _ _ xy yx

instance PartialOrder [woa : PartialOrder α] [wob : PartialOrder β] : PartialOrder (α ⊕ β) where
  le_antisymm := le_antisymm

instance decidable_le [woa : WellOrder α] [wob : WellOrder β] : DecidableRel (le : α ⊕ β → α ⊕ β → Prop)
  | Sum.inl x, Sum.inl y => 
    if h : x ≤ y
      then isTrue (le.inl h)
      else isFalse $ 
        λ hyp => match hyp with | le.inl xy => h xy
  | Sum.inr x, Sum.inr y => 
    if h : x ≤ y
      then isTrue (le.inr h)
      else isFalse $ 
        λ hyp => match hyp with | le.inr xy => h xy
  | Sum.inl _, Sum.inr _ => isTrue le.inl_inr
  | Sum.inr _, Sum.inl _ => isFalse $ λ hyp => by cases hyp

lemma le_total [woa : WellOrder α] [wob : WellOrder β] : ∀ (x y : α ⊕ β), le x y ∨ le y x
  | Sum.inl x, Sum.inl y => 
    match woa.le_total x y with
    | Or.inl xy => Or.inl (le.inl xy) 
    | Or.inr xy => Or.inr (le.inl xy) 
  | Sum.inr x, Sum.inr y => 
    match wob.le_total x y with
    | Or.inl xy => Or.inl (le.inr xy) 
    | Or.inr xy => Or.inr (le.inr xy)
  | Sum.inl x, Sum.inr y => Or.inl le.inl_inr
  | Sum.inr x, Sum.inl y => Or.inr le.inl_inr

instance WellOrder [woa : WellOrder α] [wob : WellOrder β] : WellOrder (α ⊕ β) where
  le_total := le_total
  decidable_le := decidable_le
  getMin := λ Lem P a Pa =>
    match Lem (∃ x : α, P (Sum.inl x)) with
    | isTrue ⟨a', w⟩ =>
      have ⟨x, wx⟩ := woa.getMin Lem (λ y : α => P (Sum.inl y)) a' w
      ⟨ Sum.inl x
      , wx.1
      , λ c Pc =>
        match c with
        | Sum.inl c => le.inl $ wx.2 c Pc
        | Sum.inr c => le.inl_inr 
      ⟩ 

    | isFalse h => 
      match a with
      | Sum.inl a => (h ⟨a, Pa⟩ ).elim
      | Sum.inr a => 
      have ⟨x, wx⟩ := wob.getMin Lem (λ y : β => P (Sum.inr y)) a Pa
      ⟨ Sum.inr x
      , wx.1
      , λ c Pc =>
        match c with
        | Sum.inl c => (h ⟨c, Pc⟩).elim
        | Sum.inr c => le.inr $ wx.2 c Pc
      ⟩

end Sum

section Prod

variable {α : Type u} {β : α → Type u} [poa : LinearOrder α] [pob : ∀ {α}, LinearOrder (β α)]

open Sigma

namespace Prod

inductive lt : (a : α) × β a → (a : α) × β a → Prop
  | on_fst {a₁ a₂ b₁ b₂} : a₁ < a₂ → lt ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | on_snd {a b₁ b₂} : b₁ < b₂ → lt ⟨a, b₁⟩ ⟨a, b₂⟩

open lt

inductive le : (a : α) × β a → (a : α) × β a → Prop
  | refl : le x x
  | of_lt {x y} : lt x y → le x y

lemma lt_trans {x y z : (a : α) × β a} : lt x y → lt y z → lt x z
  | on_fst xy, on_fst yz => on_fst (_root_.lt_trans xy yz)
  | on_fst xy, on_snd yz => on_fst xy
  | on_snd xy, on_fst yz => on_fst yz
  | on_snd xy, on_snd yz => on_snd (_root_.lt_trans xy yz)

lemma le_trans {x y z : (a : α) × β a} : le x y → le y z → le x z
  | p, le.refl => p
  | le.refl, p => p
  | le.of_lt xy, le.of_lt yz => le.of_lt $ lt_trans xy yz

lemma lt_irrefl : ∀ x : (a : α) × β a, ¬ lt x x
  | ⟨a, b⟩, lt.on_fst h => _root_.lt_irrefl a h
  | ⟨a, b⟩, lt.on_snd h => _root_.lt_irrefl b h

lemma lt_asymm {x y : (a : α) × β a} : lt y x → ¬ lt x y
  | on_fst yx, on_fst xy => _root_.lt_irrefl y.fst (_root_.lt_trans yx xy)
  | on_snd yx, on_fst xy => _root_.lt_irrefl y.fst xy
  | on_fst yx, on_snd xy => _root_.lt_irrefl y.fst yx
  | on_snd yx, on_snd xy => _root_.lt_irrefl y.snd (_root_.lt_trans yx xy)

lemma not_le_of_gt {x y : (a : α) × β a} : lt y x → ¬ le x y := by
  intros yx xy
  cases xy with
  | refl => exact lt_irrefl x yx
  | of_lt xy => exact lt_asymm xy yx

lemma lt_iff_le_not_le {x y : (a : α) × β a} : lt x y ↔ (le x y ∧ ¬ le y x) where
  mp := λ x_lt_y =>
    ⟨le.of_lt x_lt_y, not_le_of_gt x_lt_y⟩
  mpr := λ ⟨xy, nyx⟩ =>
    match xy with
    | le.refl => (nyx le.refl).elim
    | le.of_lt xy => xy

lemma le_antisymm {x y : (a : α) × β a} : le x y → le y x → x = y
  | le.refl, _ => rfl
  | _, le.refl => rfl
  | le.of_lt xy, le.of_lt yx => (lt_asymm xy yx).elim

lemma le_total := 

instance WellOrder : WellOrder ((a : α) × β a) where
  lt := lt
  le := le
  le_refl := λ _ => le.refl
  le_trans := λ _ _ _ xy yz => le_trans xy yz
  lt_iff_le_not_le := λ _ _ => lt_iff_le_not_le
  le_antisymm := λ x y => le_antisymm
  le_total := _
  decidable_le := _
