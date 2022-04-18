import Mathlib.Data.List.Basic

structure Queue (α : Type u) : Type u where
  front : List α
  back : List α

def push (x : α) (xs : Queue α) : Queue α := {
  front := xs.front
  back := x :: xs.back
}

def pop (x : α) (xs : Queue α) : Option (Queue α × α) :=
  match xs.front with
  | f :: fs => some ({back := xs.back, front := fs}, f)
  | [] => match xs.back.reverse with
          | b :: bs => some ({back := [], front := bs}, b)
          | nil => none

