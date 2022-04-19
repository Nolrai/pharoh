import Mathlib.Data.List.Basic
import Std.Data.Queue

namespace List

def TypeAligned {Ty} (dom cod : α → Ty) (τ σ : Ty) : List α → Prop
  | []        => τ = σ
  | (x :: xs) => τ = dom x ∧ TypeAligned dom cod (cod x) σ xs

@[simp]
lemma TypeAligned_nil : ∀ {Ty} {dom cod : α → Ty} {τ σ}, TypeAligned dom cod τ σ [] = (τ = σ) := rfl

@[simp]
lemma TypeAligned_cons : ∀ {Ty} {dom cod : α → Ty} {τ σ} {x xs}, 
  TypeAligned dom cod τ σ (x :: xs) = (τ = dom x ∧ TypeAligned dom cod (cod x) σ xs) := rfl

@[simp]
lemma TypeAligned_singleton : ∀ {Ty} {dom cod : α → Ty} {x}, 
  TypeAligned dom cod (dom x) (cod x) [x] := by simp

lemma TypeAligned_append : ∀ {ls rs : List α} {τ σ ω : Ty},
  ls.TypeAligned dom cod τ σ →
  rs.TypeAligned dom cod σ ω →
  (ls ++ rs).TypeAligned dom cod τ ω
  | nil, rs, τ, σ, ω, l_TA, r_TA => by 
    simp at *
    cases l_TA
    exact r_TA
  | cons l ls, r, τ, σ, ω, l_TA, r_TA => by
    simp at *
    cases l_TA with | intro left right =>
    apply (And.intro left)
    apply TypeAligned_append
    apply right
    exact r_TA

lemma TypeAligned_reverse (l : List α) : ∀ {τ σ : Ty}, l.TypeAligned dom cod τ σ → l.reverse.TypeAligned cod dom σ τ := by
  induction l with
  | nil => apply Eq.symm
  | cons x xs ih =>
    simp
    intros τ σ α_eq_dom_x xs_typeAligned
    apply TypeAligned_append (ih xs_typeAligned)
    rw [α_eq_dom_x]
    apply TypeAligned_singleton

end List

namespace Std.Queue

@[simp]
lemma enqueue_def (q : Queue α) : q.enqueue x = { q with eList := x::q.eList } := rfl

def TypeAligned {Ty} (dom cod : α → Ty) (τ ω : Ty) (q : Queue α) : Prop :=
  ∃ σ : Ty, q.eList.TypeAligned dom cod τ σ ∧ q.dList.TypeAligned cod dom ω σ  

lemma TypeAligned_def {Ty} {dom cod : α → Ty} {τ ω : Ty} {q : Queue α} :
  TypeAligned dom cod τ ω q = ∃ σ : Ty, q.eList.TypeAligned dom cod τ σ ∧ q.dList.TypeAligned cod dom ω σ := rfl

lemma TypeAligned_push {Ty} (dom cod : α → Ty) {ω : Ty} (x : α) (q : Queue α) :
  TypeAligned dom cod (cod x) ω q → TypeAligned dom cod (dom x) ω (q.enqueue x) := by
  intros h
  cases q
  simp
  rw [TypeAligned_def] at *
  have ⟨ω, left, right⟩ := h
  exists ω
  simp at *
  exact (And.intro left right)

def slowAppend (p q : Queue α) : Queue α where
  eList := p.eList ++ p.dList.reverse
  dList := q.dList ++ q.eList.reverse

@[simp]
lemma slowAppend_def {p q : Queue α} : 
  slowAppend p q = { eList := p.eList ++ p.dList.reverse, dList := q.dList ++ q.eList.reverse } := rfl

lemma TypeAligned_append {p q : Queue α} {cod dom : α → Ty} : 
  p.TypeAligned dom cod τ σ → 
  q.TypeAligned dom cod σ ω → 
  (p.slowAppend q).TypeAligned dom cod τ ω := by
    intros pTA qTA
    cases p with | mk peList pdList => 
    cases q with | mk qeList qdList =>
    simp
    rw [TypeAligned_def] at *
    have ⟨σ₀, pleft_, pright⟩ := pTA
    have ⟨σ₁, qleft_, qright⟩ := qTA
    simp at *
    exists σ
    constructor
    
    apply List.TypeAligned_append pleft_
    apply List.TypeAligned_reverse
    apply pright

    apply List.TypeAligned_append qright
    apply List.TypeAligned_reverse
    apply qleft_

end Queue






