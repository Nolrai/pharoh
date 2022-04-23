import Mathlib

inductive Down : Type (u + 1) where
  | Zero : Down
  | Limit (elems : ℕ → Down) : Down

namespace Down
open Down

def succ (n : Down) : Down := Limit (λ _ => n)

def ofNat : Nat → Down 
  | 0 => Zero
  | (n+1) => succ (ofNat n)

instance : OfNat Down n := ⟨ofNat n⟩

inductive mem : Down → Down → Prop :=
  | intro (f : ℕ → Down) (n) : mem (f n) (Limit f)

def isToFrom x y (l : List α) := l.head? = some x ∧ l.last' = some y

def isChain (l : List Down) :=
    ∀ n x' y', l.get? n = some x' → l.get? (n+1) = some y' -> mem x' y'

def le (x y : Down) := 
  ∃ l : List Down, isToFrom x y l ∧ isChain l

def lt x y :=
  ∃ l : List Down, isToFrom x y l ∧ isChain l ∧ l.length ≥ 2

def le_aux : List α → List α → List α
  | l, [] => l
  | l, x :: xs => l ++ xs

@[simp]
lemma le_aux_nil (l : List α ) : le_aux l [] = l := rfl

@[simp]
lemma le_aux_cons (x : α ) : le_aux l (x :: xs) = l ++ xs := rfl

@[simp]
lemma head_le_aux (l : List α) : l ≠ [] → (le_aux l l').head? = l.head? := by
  intros h
  cases l'
  cases l
  simp
  rw [le_aux_nil]; simp
  cases l
  exfalso; apply h; apply rfl
  simp

@[simp] 
lemma last_cons : ∀ {xs : List α}, xs ≠ [] -> (x :: xs).last' = xs.last'
  | [], h => by exfalso; apply h; apply rfl
  | x :: xs, _ => by
    simp

@[simp] 
lemma last_append : ∀ (l l' : List α), l' ≠ [] → (l ++ l').last' = l'.last'
  | l, [], h => (h rfl).elim
  | [], y :: yz, h => by simp
  | x :: xs, y :: ys, h => by
    simp
    apply last_append _ _ h

lemma get?_last_aux : ∀ {n} {l : List α}, n + 1 = l.length → l.get? n = l.last'
  | 0, [x], rfl => rfl
  | (n + 1), x :: xs, p => by
    simp at p
    rw [p]
    simp
    cases xs with
    | nil => rfl
    | cons xs xss =>
      rw [last_cons]
      simp
      have : xss.length = (xs::xss).length - 1 := rfl
      rw [this]
      have p' : n + 1 = (xs :: xss).length := by simp at p; rw [p]; simp
      rw [← get?_last_aux p', ← p', Nat.add_sub_cancel]
      simp

@[simp]
lemma get?_last : ∀ (l : List α), l.get? (l.length - 1) = l.last' 
  | [] => rfl 
  | x :: xs => by 
    apply get?_last_aux
    simp
    apply Nat.add_sub_cancel _ 1

@[simp] 
lemma last_le_aux : ∀ (l l' : List α), l'.length > 1 → (le_aux l l').last' = l'.last'
  | l, [], h => by simp at *
  | l, [x], h => by simp at *
  | l, x :: xs :: xss, h => by simp

lemma le_trans_list_length_aux {y : α} {ys yss} : List.length (y :: ys :: yss) > 1 :=
  show 1 < yss.length.succ.succ from
  show 1 < yss.length + 2 by
  apply lt_of_lt_of_le
  show 1 < 2
  simp
  apply Nat.le_add_left

lemma le_trans_isToFrom
  {x xs y ys : Down}
  {xss yss : List Down}
  (last_lxy : List.last' (x :: xs :: xss) = some y)
  (last_lyz : List.last' (y :: ys :: yss) = some z)
  : isToFrom x z (le_aux (x :: xs :: xss) (y :: ys :: yss)) := by
    apply And.intro
    rw [head_le_aux]
    simp
    simp
    rw [last_le_aux, last_cons]
    assumption
    simp
    apply le_trans_list_length_aux

lemma some_ext (x y : α) : some x = some y → x = y
  | rfl => rfl

lemma le_trans_isChain_aux : ∀ (x y : ℕ), Decidable (x ≤ y)
  | 0, y => isTrue (Nat.zero_le y)
  | n+1, 0 => isFalse $ by 
    rw [Nat.le_zero_iff]
    intros h; cases h
  | n+1, m+1 => 
    match le_trans_isChain_aux n m with
    | isTrue h => isTrue (Nat.add_le_add_right h 1)
    | isFalse h => isFalse λ h' => h (Nat.le_of_succ_le_succ h')

lemma le_trans_isChain
  (last_lxy : List.last' xy = some y)
  (lxy_isChain : isChain xy)
  (lyz_isChain : isChain (y :: yzs))
  : isChain (le_aux xy (y :: yzs)) := λ n x' y' =>
    match Nat.lt_trichotomy (n+1) (xy.length) with
    | Or.inl h => by
      simp at *
      rw [List.get?_append, List.get?_append]
      intros getn getn_one
      apply lxy_isChain _ _ _ getn getn_one
      exact h
      apply lt_trans (Nat.lt_succ_self _) h
    | Or.inr h => by
      simp at *
      cases h with
      | inr h =>
        rw [List.get?_append_right, List.get?_append_right]
        intros getn getn_one
        cases (le_trans_isChain_aux _ _ : Decidable (List.length yzs ≤ n + 1 - List.length xy)) with
        | isTrue h2 => 
          rw [List.get?_len_le] at getn_one
          cases getn_one
          exact h2
        | isFalse h2 =>
          apply lyz_isChain (n - xy.length + 1)
          simp
          exact getn
          simp
          have : (n + 1 - xy.length) = (n - xy.length) + 1 := by
            rw [← Nat.add_comm 1, Nat.add_sub_assoc, ← Nat.add_comm 1]
            apply Nat.le_of_lt_succ h
          rw [this] at getn_one
          simp at getn_one
          exact getn_one
        simp
        apply le_of_lt h
        apply Nat.le_of_lt_succ h
      | inl h =>
        simp
        intros getn getn_one
        rw [List.get?_append,] at getn
        rw [List.get?_append_right] at getn_one
        apply lyz_isChain
        rw [List.get?_zero]
        simp
        apply some_ext
        intros
        rw [← getn, ← last_lxy]
        rw [← get?_last, ← h]
        apply congr_arg
        apply Eq.symm
        apply Nat.add_sub_cancel n 1

        rw [← getn_one, h]
        simp
        rw [h]
        apply le_refl
        apply Nat.lt_of_succ_le
        rw [← h]
        apply le_refl

lemma le_trans {x y z} : le x y → le y z → le x z
  | ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain⟩, ⟨lyz, ⟨head_lyz, last_lyz⟩, lyz_isChain⟩ =>
    match lxy, lyz with
    | [], _ => by simp at *
    | _, [] => by simp at *
    | [x'], _ =>
      have some_x_eq_some_y : some x = some y := by 
        rw [← head_lxy, ← last_lxy]
        simp
      have : x = y := by
        injection some_x_eq_some_y
        assumption
      by
        simp
        rw [this]
        assumption
    | _, [y'] =>
      have some_y_eq_some_z : some y = some z := by 
        rw [← head_lyz, ← last_lyz]
        simp
      have : y = z := by
        injection some_y_eq_some_z
        assumption
      by
        simp
        rw [← this]
        assumption
    | _::xs::xss, _::ys::yss => by
      simp at head_lxy head_lyz
      cases head_lxy
      cases head_lyz
      apply Exists.intro (le_aux (x::xs::xss) (y::ys::yss))
      apply And.intro
      apply le_trans_isToFrom last_lxy last_lyz
      apply le_trans_isChain last_lxy lxy_isChain lyz_isChain

lemma not_lt_Zero_aux (x : Down) (l : List Down) : ¬ isChain (l ++ [x, Zero]) := by
  induction l with
  | nil => 
    simp
    intros h
    have h' := h 0 x Zero rfl rfl
    cases h'
  | cons y ys ys_ih =>
    intros h
    apply ys_ih
    intros n a b getn getn_one
    apply h (n+1)
    rw [← getn]
    simp
    rw [← getn_one]
    simp



lemma le_refl : ∀ x, le x x 
  | x => ⟨[x], by
    intros
    apply And.intro
    apply ⟨rfl, rfl⟩
    intros n x' y' x'h y'h
    exfalso
    simp at *
  ⟩

lemma isChain_up (x : Down) (xs : List Down) : isChain (x :: xs) → isChain xs := by
  intros h n x' y' getn getn_one
  apply h (n+1)
  rw [← getn]
  simp
  rw [← getn_one]
  simp

lemma not_mem_zero : ∀ a, ¬ mem a Zero
  | a, h => by cases h

lemma le_Zero (a : Down) (h : le a Zero) : a = Zero := 
  have ⟨l, ⟨l_head, l_last⟩, l_isChain⟩ := h
  by
  apply some_ext
  rw [← l_head]
  clear l_head
  induction l with
  | nil => simp at l_last
  | cons x xs xs_ih => 
    cases xs with
    | nil => 
      simp at *
      exact l_last
    | cons xs xss =>
        simp at *
        have xs_eq_Zero : xs = Zero := by {apply xs_ih l_last; apply isChain_up _ _ l_isChain}
        cases xs_eq_Zero
        exfalso
        apply not_mem_zero x
        apply l_isChain 0 x Zero
        simp
        simp 
lemma le_Zero_iff (a : Down) : le a Zero ↔ a = Zero where
  mpr h := by cases h; apply le_refl
  mp h := le_Zero a h

lemma Zero_Chains_aux : ∀ n l, (l.length = n) → (l.last' = some Zero) → isChain l → l = [Zero]
  | 0, [], rfl, l_last, l_isChain => by simp at l_last
  | 1, [x], l_length, l_last, l_isChain => by
    simp at l_last
    rw [l_last]
  | (n+2), x::xs::xss, l_length, l_last, l_isChain => by
    simp at *
    have : xs::xss = [Zero] := by 
      apply (Zero_Chains_aux (n+1) (xs::xss))
      simp; exact l_length
      exact l_last
      apply isChain_up x _ l_isChain
    simp
    rw [this] at l_isChain
    apply not_mem_zero x
    apply l_isChain 0 x Zero
    simp
    simp

lemma Zero_Chains (l : List Down) : l.last' = Zero → isChain l → l = [Zero] := Zero_Chains_aux l.length l rfl


    

lemma lt_iff_le_not_le (a b : Down) : lt a b ↔ (le a b ∧ ¬(le b a)) where
  mp h := 
    match h with
    | ⟨l, lh⟩ => ⟨⟨l, lh.1, lh.2.1⟩, _⟩
  mpr := _
      
instance : PartialOrder Down := {
  le := le
  lt := lt
  le_refl := le_refl 
  le_trans := λ _ _ _ => le_trans
  le_antisymm := le_antisymm
  lt_iff_le_not_le := _
}