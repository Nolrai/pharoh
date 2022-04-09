import Init.Control
import Mathlib.Data.Fin.Basic

namespace lambda

inductive lambda (V : Type u) where
  | Var (_ : V)
  | App (f arg : lambda V)
  | Abs (body : V → lambda V)

open lambda

abbrev Term := ∀ {V}, lambda V

def lambda_id : Term := Abs (λ x => Var x)

def numVars_aux : lambda Unit → ℕ 
  | Var _ => 1
  | App f x => numVars_aux f + numVars_aux x
  | Abs body => numVars_aux (body ())

abbrev numVars (e : Term) : ℕ := numVars_aux e

def canEta_aux2 : lambda Bool → Bool
  | Var b => b
  | App f x => canEta_aux2 f && canEta_aux2 x
  | Abs body => canEta_aux2 (body true)

def canEta_aux
  | Abs e' =>
    match e' false with
    | App e₁ (Var false) => canEta_aux2 e₁
    | _ => false
  | _ => false

abbrev canEta (e : Term) : Bool := canEta_aux e

abbrev Term1 := ∀ ⦃V⦄, V → lambda V

def subst {V} : lambda (lambda V) → lambda V
  | Var e => e
  | App f x => App (subst f) (subst x)
  | Abs body => Abs (λ x => subst (body (Var x)))

abbrev Subst : Term1 → Term → Term :=
  λ E₁ E₂ => subst (E₁ E₂) 

abbrev appV {V} (f x : V) : lambda V := App (Var f) (Var x)

def zero : Term := 
  λ {V} => 
    Abs (λ f : V => lambda_id)

def one : Term :=
  λ {V} =>
    Abs (λ f : V => Abs (λ x : V => appV f x))

def comp : Term :=
  λ {V} =>
    Abs (λ f : V => Abs (λ g : V => Abs (λ x : V => App (Var f) (appV g x))))

def add : Term :=
λ {V} =>
    Abs (λ n : V => 
    Abs (λ m : V => 
    Abs (λ f : V => 
      App (App comp (appV n f)) (appV m f)
    )))

def mul : Term :=
λ {V} =>
    Abs (λ n : V => 
    Abs (λ m : V => 
    Abs (λ f : V => 
      App (Var n) (appV m f)
    )))

def getF (V) : Term -> OptionM (lambda V -> lambda (lambda V)) :=
  fun t =>
  match @t (lambda V) with
      | App (Abs f) _ => some f
      | _ => none

def getCoArg (V) : lambda V -> OptionM (lambda V) :=
  fun t =>
  match t with
      | App coArg _ => some coArg
      | _ => none

def getArg (V) : lambda V -> OptionM (lambda V) :=
  fun t =>
  match t with
      | App _ arg => some t
      | _ => none

def beta' (t : Term) {V} : OptionM (lambda V) :=
  do
    let f <- getF V t
    let arg <- getArg V t
    pure (subst (f arg))

def beta_aux {α : Type} (default : α) : OptionM α → α 
  | some a => a
  | none => default

def do_beta (t : Term) : Term :=
  λ {V} => beta_aux t (beta' t)

def app : Term → Term → Term :=
  fun f x {V} => App f x

def two : Term := app (app add one) one

inductive NatAux where
  | nat : ℕ → NatAux
  | suc : NatAux

open NatAux

abbrev nat' n := Var (nat n)
abbrev suc' := Var suc

