import Mathlib.Data.List.Basic
import Pharoh.Queue

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

namespace Queue

def TypeAligned {Ty} (dom cod : α → Ty) (τ σ : Ty) (q : Queue α) : Prop :=
  ∃ ω : Ty, q.back.TypeAligned cod dom τ ω ∧ q.front.TypeAligned dom cod σ ω

end Queue






