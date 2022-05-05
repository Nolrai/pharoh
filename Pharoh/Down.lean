import Mathlib
import Init.Data.Range

lemma List.get?_succ (n : ℕ) (x : α) (xs : List α) : (x :: xs).get? (n + 1) = xs.get? n := by
  simp

def Sequence α := ℕ → α

namespace Sequence

def tail : Sequence α → Sequence α :=
  λ s n => s (n + 1)

@[simp]
def tail_def (s : Sequence α) : s.tail n = s (n+1) := rfl

def take : ℕ → (Sequence α) → List α 
  | 0 => λ _ => []
  | n + 1 => λ s => s 0 :: s.tail.take n

@[simp]
def take_zero (s : Sequence α) : s.take 0 = [] := rfl

@[simp]
def take_succ (s : Sequence α) : s.take (n + 1) = s 0 :: s.tail.take n := rfl

lemma take_length : ∀ n (s : Sequence α), (s.take n).length = n
  | 0, s => rfl
  | (n+1), s => by
    simp
    apply take_length n

@[simp]
lemma get?_take_aux : ∀ n ix (s : Sequence α), ix < n → List.get? (s.take n) ix = some (s ix)
  | 0, _, s, p => by exfalso; apply Nat.not_lt_zero _ p
  | (Nat.succ n), 0, s, _ => by simp
  | (Nat.succ (Nat.succ n)), (Nat.succ ix), s, p => by
    rw [Sequence.take_succ]
    rw [List.get?_succ]
    rw [get?_take_aux (n+1)]
    simp
    rw [Nat.add_one] at *
    apply Nat.lt_of_succ_lt_succ p

abbrev get?_take (s : Sequence α) : ∀ n ix, ix < n → List.get? (s.take n) ix = some (s ix) := 
  λ n ix => get?_take_aux n ix s

end Sequence

open Sequence

def List.cycle : ∀ l : List α, l.length > 0 → Sequence α :=
  λ l p n => l.get ⟨n % l.length, Nat.mod_lt _ p⟩

@[simp]
def Sequence.cycle_def' (l : List α) (p : l.length > 0) : 
  l.cycle p n = l.get ⟨n % l.length, Nat.mod_lt _ p⟩ := rfl

@[simp]
def Sequence.cycle_def (l : List α) (p : l.length > 0) : 
  l.cycle p = λ n => l.get ⟨n % l.length, Nat.mod_lt _ p⟩ := by
  funext n
  simp

def some_ext (a b : α) : some a = some b → a = b := λ p => by cases p; rfl

lemma List.length_init_aux : ∀ (n : ℕ) (l : List α), l.length = n → l.init.length = l.length - 1
  | 0, [], _ => rfl
  | 1, [x], _ => rfl
  | (n+2), x :: xs :: xss, p => by
    simp at *
    rw [← Nat.add_one, ← Nat.add_one, Nat.add_sub_cancel]
    simp
    rw [length_init_aux (n+1) (xs :: xss)]
    simp [← Nat.add_one, Nat.add_sub_cancel]
    simp
    exact p

lemma List.length_init (l : List α) : l.init.length = l.length - 1 :=
  l.length_init_aux l.length rfl

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

def mem : Down → Down → Prop
  | d, Limit f => ∃ n, d = f n
  | d, Zero => False

lemma mem_Limit : ∀ {d f}, mem d (Limit f) = ∃ n, d = f n := rfl

@[simp]
lemma mem_Zero : ∀ {d}, mem d Zero = False := rfl

def isToFrom x y (l : List α) := l.head? = some y ∧ l.last' = some x

def isChain (l : List Down) :=
    ∀ n x' y', l.get? n = some x' → l.get? (n+1) = some y' -> mem y' x'

@[simp]
lemma isChain_nil : isChain []
  | n, x', y', x'h, y'h => by simp at *

def le (x y : Down) := 
  ∃ l : List Down, isToFrom x y l ∧ isChain l

def lt x y :=
  ∃ l : List Down, isToFrom x y l ∧ isChain l ∧ l.length ≥ 2

lemma List.more_than_two  {z zs : α} {zss : List α} : (z :: zs :: zss).length ≥ 2 := by
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply Nat.zero_le

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


lemma not_mem_Zero : ∀ a, ¬ mem a Zero
  | a, h => by cases h

lemma not_lt_Zero_aux (x : Down) (l : List Down) : ¬ isChain ([Zero, x] ++ l)
  | h => not_mem_Zero _ (h 0 Zero x rfl rfl)

lemma le_refl : ∀ x, le x x 
  | x => ⟨[x], by
    intros
    apply And.intro
    apply ⟨rfl, rfl⟩
    intros n x' y' x'h y'h
    exfalso
    simp at *
  ⟩

lemma isChain_down (x : Down) (xs : List Down) : isChain (x :: xs) → isChain xs := by
  intros h n x' y' getn getn_one
  apply h (n+1)
  rw [← getn]
  simp
  rw [← getn_one]
  simp

lemma Zero_Chains : ∀ (l : List Down), l.head? = some Zero → isChain l → l = [Zero]
  | [], l_head, l_isChain => by cases l_head
  | [x], l_head, l_isChain => by simp at *; exact l_head
  | x :: xs :: xss, l_head, l_isChain => by 
    simp at *
    cases l_head
    exfalso
    apply not_mem_Zero xs
    apply l_isChain 0 Zero xs rfl rfl

lemma le_Zero : ∀ (a : Down) (h : le a Zero), a = Zero
  | a, ⟨l, ⟨l_head, l_last⟩, l_isChain⟩ => 
    have : l = [Zero] := Zero_Chains l l_head l_isChain
    by
    cases this
    cases l_last
    apply rfl

lemma le_Zero_iff (a : Down) : le a Zero ↔ a = Zero where
  mpr h := by cases h; apply le_refl
  mp h := le_Zero a h

open Sequence

lemma decending_chain_conditon : ∀ (s : Sequence Down), ¬ ∀ n, isChain (s.take n) := by
  intros s
  let h : ∃ a, s 0 = a := ⟨s 0, rfl⟩
  cases h with | intro a ah =>
  clear h
  revert s
  induction a with
  
  | Zero =>
    intros s ah impossible
    apply not_mem_Zero (s 1)
    have h := impossible 2
    simp at h
    rw [ah] at h
    apply h 0
    simp
    simp

  | Limit elems elems_ih => 
    intros s ah impossible
    have h : mem (s 1) (Limit elems) := by 
      apply (impossible 2 0)
      simp
      exact ah
      simp
    rw [mem_Limit] at h
    cases h with | intro ix ix_h =>
    simp
    apply elems_ih ix (s.tail) ix_h
    intros n
    cases n with
    | zero => simp
    | succ n' => 
      apply isChain_down (s 0)
      have : Sequence.take (n'.succ.succ) s = (s 0 :: s.tail.take n'.succ) := rfl
      rw [← this]
      apply impossible

lemma lt_strongly_antisymm'_aux : ∀ n, n ≥ 2 → n - 1 > 0
  | Nat.succ (Nat.succ n), p => by
    rw [← Nat.add_one]
    rw [Nat.add_sub_cancel]
    apply Nat.gt_of_not_le
    apply Nat.not_lt_zero
    
lemma not_mem_self {a} : ¬ mem a a :=
  by
  induction a with
  | Zero => simp
  | Limit elems elems_ih =>
    intros h
    have h' := h
    rw [mem_Limit] at h
    have ⟨n, h⟩ := h
    apply elems_ih n
    rw [←h]
    apply h'

lemma List.get?_init {α} : ∀ (ix : ℕ) (l : List α) (ix_neq : ix ≠ l.init.length), l.get? ix = l.init.get? ix
  | _, [], _ => rfl
  | (n+1), [x], refl => rfl 
  | 0, x::xs::xss, _ => rfl
  | (n+1), x::xs::xss, ix_neq => by
    match lt_trichotomy (n+1) (x::xs::xss).init.length with
    | Or.inr (Or.inl h) => simp; exact (ix_neq h).elim
    | (Or.inl h) => simp at *; apply get?_init; exact ix_neq
    | Or.inr (Or.inr h) => simp at *; apply get?_init; exact ix_neq

lemma List.head_init {α} : ∀ (l : List α), l.length > 1 → l.init.head? = l.head?
  | x :: y :: l, p => by simp 
  | [x], p => by simp at p
  | [], p => by simp at p

lemma lt_strongly_antisymm' (a : Down) : ¬ lt a a := 
  λ h => 
    have ⟨l, ⟨l_head, l_last⟩, l_isChain, l_length⟩ := h
    have l_init_length : l.init.length > 1 :=
      match l with
      | [] => by simp at *
      | [x] => by simp at *
      | [x, y] => by
        cases l_head; cases l_last
        exfalso
        apply not_mem_self (l_isChain 0 a a rfl rfl)
      | _::_::_::_ => by 
        simp at *
        apply Nat.succ_lt_succ
        rw [Nat.add_one]
        apply Nat.zero_lt_succ
    have l_init_length' : l.init.length > 0 := Nat.lt_trans Nat.zero_lt_one l_init_length 
    have ⟨s, sh⟩ : ∃ s : Sequence Down, s = l.init.cycle l_init_length' := ⟨l.init.cycle l_init_length', rfl⟩
    have neq_of_lt : ∀ n m : ℕ, n < m → n ≠ m := by
      clear s sh
      intros n m h
      rw [lt_iff_le_not_le] at h
      intros h'
      cases h'
      apply h.2
      apply Nat.le_refl
    by
      apply decending_chain_conditon s
      rw [sh]
      intros n ix x' y' xh yh
      cases Nat.decLt (ix + 1) n with
      | isFalse h => 
        exfalso
        apply h; clear h
        rw [List.get?_eq_some] at *
        have h' := yh.1
        rw [take_length] at h'
        exact h'
     
      | isTrue ix_one_lt_n =>
        have ix_lt_n : ix < n := by apply Nat.lt_trans (Nat.lt_succ_self ix) ix_one_lt_n 
        rw [get?_take _ _ _ ix_lt_n] at xh
        rw [get?_take _ _ _ ix_one_lt_n] at yh
        have x'h := some_ext _ _ xh
        have y'h := some_ext _ _ yh
        rw [← y'h, ← x'h]
        clear x' y' xh yh x'h y'h
        rw [Sequence.cycle_def' l.init l_init_length', Sequence.cycle_def' l.init l_init_length']

        apply l_isChain (ix % l.init.length)
        case a =>
          rw [← List.get?_eq_get, ← List.get?_init]
          simp
          apply neq_of_lt
          apply Nat.mod_lt
          apply l_init_length'
        
        rw [← List.get?_eq_get]
          
        rw [Nat.add_mod]
          have : 1 % l.init.length = 1 := by apply Nat.mod_eq_of_lt l_init_length
          rw [this]; clear this 
          
        have h : 
          (ix % l.init.length + 1 < l.init.length) ∨ (ix % l.init.length + 1 = l.init.length) := 
            le_iff_lt_or_eq.mp (Nat.succ_le_of_lt (Nat.mod_lt _ l_init_length'))
        cases h with
        | inl h =>
          rw [← List.get?_init ]
          apply congr_arg
          apply Eq.symm
          apply Nat.mod_eq_of_lt h
          apply neq_of_lt
          apply Nat.mod_lt
          exact l_init_length'
        | inr h =>
          rw [h, List.length_init, get?_last, l_last]
          rw [← List.length_init]
          rw [Nat.mod_self, List.get?_zero, ← l_head]
          apply Eq.symm
          apply List.head_init 
          apply l_length

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
  {y ys z zs : Down}
  {yss zss : List Down}
  (last_lxy : List.last' (y :: ys :: yss) = some x)
  (last_lyz : List.last' (z :: zs :: zss) = some y)
  : isToFrom x z (le_aux (z :: zs :: zss) (y :: ys :: yss)) := by
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
        apply Nat.le_refl
        apply Nat.lt_of_succ_le
        rw [← h]
        apply Nat.le_refl

lemma lt_trans : ∀ {x y z}, lt x y → lt y z → lt x z
  | x, y, z, 
    ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain, lxy_length⟩, 
    ⟨lyz, ⟨head_lyz, last_lyz⟩, lyz_isChain, lyz_length⟩ =>
    match lxy, lyz with
    | _::ys::yss, _::zs::zss  => by
      simp at head_lxy head_lyz
      cases head_lxy
      cases head_lyz
      apply Exists.intro (le_aux (z::zs::zss) (y::ys::yss))
      apply And.intro
      apply le_trans_isToFrom last_lxy last_lyz
      apply And.intro
      apply le_trans_isChain last_lyz lyz_isChain lxy_isChain
      rw [le_aux_cons, List.cons_append, List.cons_append]
      apply List.more_than_two

lemma lt_strongly_antisymm : ∀ a b, lt a b → ¬ lt b a
  | a, b, a_lt_b, b_lt_a => lt_strongly_antisymm' a (lt_trans a_lt_b b_lt_a)

lemma le_antisymm  (a b : Down) : le a b → le b a → a = b
  | ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain⟩, ⟨lyx, ⟨head_lyx, last_lyx⟩, lyx_isChain⟩ =>
    match lxy, lyx with
    | [], _ => by simp at *
    | _, [] => by simp at *
    | [_], _ => by 
      simp at *
      apply Eq.trans last_lxy.symm head_lxy
    | _, [_] => by 
      simp at *
      apply Eq.trans head_lyx.symm last_lyx
    | _::ys::yss, _::zs::zss  => by
      have head_lxy' : _ = b := by
        simp at head_lxy
        exact head_lxy
      have head_lyx' : _ = a := by
        simp at head_lyx
        exact head_lyx
      cases head_lxy'
      cases head_lyx'
      exfalso
      apply lt_strongly_antisymm a b
      exact ⟨_, ⟨head_lxy, last_lxy⟩, lxy_isChain, List.more_than_two⟩
      exact ⟨_, ⟨head_lyx, last_lyx⟩, lyx_isChain, List.more_than_two⟩

lemma le_trans {x y z} : le x y → le y z → le x z
  | ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain⟩, ⟨lyz, ⟨head_lyz, last_lyz⟩, lyz_isChain⟩ =>
    match lxy, lyz with
    | [], _ => by simp at *
    | _, [] => by simp at *
    | [x'], lyz =>
      have some_x_eq_some_y : some x = some y := by 
        rw [← head_lxy, ← last_lxy]
        simp
      have : x = y := by
        injection some_x_eq_some_y
        assumption
      by
        simp
        rw [this]
        exact ⟨lyz, ⟨head_lyz, last_lyz⟩, lyz_isChain⟩
    | lxy, [y'] =>
      have some_y_eq_some_z : some y = some z := by 
        rw [← head_lyz, ← last_lyz]
        simp
      have : y = z := by
        injection some_y_eq_some_z
        assumption
      by
        rw [← this]
        exact ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain⟩
    | _::ys::yss, _::zs::zss  => by
      simp at head_lxy head_lyz
      cases head_lxy
      cases head_lyz
      apply Exists.intro (le_aux (z::zs::zss) (y::ys::yss))
      apply And.intro
      apply le_trans_isToFrom last_lxy last_lyz
      apply le_trans_isChain last_lyz lyz_isChain lxy_isChain

lemma lt_iff_le_not_le (a b : Down) : lt a b ↔ le a b ∧ ¬ le b a := 
{ mp := λ ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain, lxy_long⟩ =>
  have le_b_a := ⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain⟩
  ⟨ le_b_a 
  , λ h2 => 
    let a_eq_b : a = b := le_antisymm _ _ le_b_a h2
    by 
    cases a_eq_b
    apply lt_strongly_antisymm a a _ _
    assumption
    assumption
  ⟩

, mpr := λ ⟨⟨lxy, ⟨head_lxy, last_lxy⟩, lxy_isChain⟩, not_le_b_a⟩ =>
    have a_neq_b : a ≠ b := by
      intros h
      apply not_le_b_a
      rw [h]
      apply Down.le_refl
    match lxy with
    | [] => by 
      simp at *
    | [x] => by 
      simp at *
      exfalso
      apply a_neq_b
      apply Eq.trans last_lxy.symm head_lxy
    | x::xs::xss =>
      ⟨x::xs::xss, ⟨head_lxy, last_lxy⟩, lxy_isChain, List.more_than_two⟩
}

instance : PartialOrder Down := {
  le := Down.le
  lt := Down.lt
  le_refl := Down.le_refl
  le_trans := λ _ _ _ => Down.le_trans
  le_antisymm := Down.le_antisymm
  lt_iff_le_not_le := Down.lt_iff_le_not_le
}

lemma mem_lt (h : mem a b) : a < b :=
  have ba_isChain : isChain [b, a] := by
    intros n x' y' xh yh
    cases n with
    | succ n => simp at *
    | zero => 
      simp at *
      cases xh
      cases yh
      exact h
  ⟨[b, a], ⟨rfl, rfl⟩, ba_isChain, Nat.le_refl 2⟩ 

lemma not_lt_zero : ∀ (a : Down), ¬ a < 0
  | Zero, h => by
    rw [_root_.lt_iff_le_not_le] at h
    apply h.2 (le_refl 0)
  | Limit elems, ⟨[], ⟨l_head, l_tail⟩, l_chain, l_length⟩ => by simp at l_length
  | Limit elems, ⟨[x], ⟨l_head, l_tail⟩, l_chain, l_length⟩ => by simp at l_length
  | Limit elems, ⟨_::xs::xss, ⟨l_head, l_tail⟩, l_chain, l_length⟩ => by
    simp at *
    cases l_head
    apply not_mem_Zero xs
    apply l_chain 0 0 xs rfl rfl

lemma zero_le : ∀ a : Down, 0 ≤ a
  | Zero => le_refl 0
  | Limit a => by
    apply _root_.le_trans (zero_le (a 0)) (le_of_lt (mem_lt _))
    exists 0

universe u

-- lemma strong_induction_aux 
--   (P : Down → Prop) 
--   (P_lt : ∀ a, (∀ b, b < a → P b) → P a)
--   : ∀ x y, y ≤ x → P y := by


  -- | _, Zero, _ => P_lt Zero (λ b b_lt => (not_lt_zero b b_lt).elim)
  -- | Zero, y, h => by
  --   rw [le_iff_lt_or_eq] at h
  --   cases h with
  --   | inl h => exfalso; apply not_lt_zero _ h
  --   | inr h => 
  --     cases h
  --     apply strong_induction_aux _ P_lt
  --     apply zero_le Zero
  -- | Limit elems_x, Limit elems_y, ⟨l, ⟨l_head, l_tail⟩, l_chain⟩ => 
  --   match l with
  --   | [] => by simp at *
  --   | [x] => by simp at *

  -- intros x
  -- induction x with
  -- | Zero =>
  --   intros y yh
  --   rw [le_iff_lt_or_eq] at yh
  --   cases yh with
  --   | inl h => exfalso; apply not_lt_zero _ h
  --   | inr h => 
  --     cases h
  --     apply strong_induction_aux _ P_lt
  --     apply zero_le Zero
  -- | Limit elems elems_ih =>
  --   intros y yh
  --   have ⟨l, ⟨l_head, l_tail⟩, l_chain⟩ := yh
  --   cases l with
  --   | nil => simp at *
  --   | cons x xs =>
  --     cases l with
