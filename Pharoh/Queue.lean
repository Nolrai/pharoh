import Mathlib.Data.List.Basic

structure Queue (α : Type u) : Type u where
  front : List α
  back : List α

namespace Queue

instance : EmptyCollection (Queue α) := ⟨⟨[],[]⟩⟩

@[simp]
lemma empty_def : (∅ : Queue α) = ⟨[], []⟩ := rfl 

def push (x : α) (xs : Queue α) : Queue α :=
  {xs with back := x :: xs.back}

@[simp]
lemma push_def {x : α} : push x xs = {xs with back := x :: xs.back} := rfl 

def pop (xs : Queue α) : Option (Queue α × α) :=
  match xs.front with
  | f :: fs => some ({back := xs.back, front := fs}, f)
  | [] => match xs.back.reverse with
          | b :: bs => some ({back := [], front := bs}, b)
          | nil => none

@[simp]
lemma pop_cons {f : α} {bs fs : List α} : 
  pop {back := bs, front := f :: fs} = some (({back := bs, front := fs} : Queue α), f) := rfl

@[simp]
lemma pop_empty : pop (∅ : Queue α) = none := rfl

theorem exists_head_of_reverse {bs : List α} (bsNotNil : bs ≠ []) : ∃ b' bs', bs.reverse = b' :: bs' := by
  induction bs with
  | nil => 
    exfalso
    apply bsNotNil rfl
  | cons x xs ih =>
    cases xs with
    | nil => 
      exists x; exists []; simp
    | cons head tail =>
      simp at *
      cases ih with | intro b' ih =>
      cases ih with | intro bs' ih =>
      exists b'
      exists (bs' ++ [x])
      rw [ih]
      simp

theorem pop_flip_aux {bs : List α} :
  pop {back := bs, front := []} = 
          ( match bs.reverse with
            | b :: bs => some ({back := [], front := bs}, b)
            | nil => none
          ) := by
  rfl

@[simp]
lemma pop_flip {bs : List α} :
  pop {back := bs, front := []} = pop {back := [], front := bs.reverse} := by
    cases bs with
    | nil => 
      rw [List.reverse_nil, ← empty_def, pop_empty]
    | cons b bs =>
      have h := exists_head_of_reverse (List.noConfusion : (b :: bs) ≠ [])
      cases h with | intro b' h =>
      cases h with | intro bs' h =>
      rw [pop_flip_aux, h]
      simp

end Queue