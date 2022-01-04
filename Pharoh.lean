import Init.Control

namespace lambda

abbrev ℕ := Nat

inductive lambda (V : Type) where
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

def getF (V) : Term -> OptionT Id (lambda V -> lambda (lambda V)) :=
  fun t =>
  match @t (lambda V) with
      | App (Abs f) _ => some f
      | _ => none

def getX (V) : Term -> OptionT Id (lambda V) :=
  fun t =>
  match @t V with
      | App _ x => some x
      | _ => none

def beta' (t : Term) {V} : OptionT Id (lambda V) :=
  do
    let f <- getF V t
    let x <- getX V t
    pure (subst (f x))

def beta_aux {α : Type} (default : α) : OptionT Id α → α 
  | some a => a
  | none => default

def do_beta (t : Term) : Term :=
  λ {V} => beta_aux t (beta' t)

def app : Term → Term → Term :=
  fun f x {V} => App f x

inductive lazy_aux : Term → Term → Prop
  | beta : ∀ x : Term, lazy_aux x (do_beta x)
  | head : ∀ x y z : Term, lazy_aux x y → lazy_aux (app x z) (app y z)

infix:50 " ⇒ " => lazy_aux

inductive lazy : Term → Term → Prop
  | refl {x : Term} : lazy x x
  | snoc (x : Term) (y : Term) (z : Term) : lazy x y → y ⇒ z → lazy x z

infix:50 " ⇒* " => lazy

theorem lazy.symm (x : Term) : ∀ (y : Term), x ⇒* y → y ⇒* x
  | _, refl => _

def equiv : Term → Term → Prop :=
  λ x y => ∃ z : Term, x ⇒* z ∧ y ⇒* z

theorem equiv_is_eqv : Equivalence equiv := by
  constructor
  case refl => 
    intro x
    exists x
    apply And.intro lazy.refl lazy.refl
  case symm =>
    intros x y equiv_xy
    cases equiv_xy with
    | intro h w => 
      cases w with
      | intro hyp_x hyp_y =>
        exists h
        exact And.intro hyp_y hyp_x
  case trans =>
    intros x y z xy yz
    cases xy with
      | intro w hyp_xy => _
      cases hyp_xy with
        | intro hyp_xw hyp_yw =>
        cases hyp_xw

instance Term_Setoid : Setoid Term where
  r := equiv
  iseqv := 
    by constructor
    case refl 
     

def two : Term := app (app add one) one


 



end lambda