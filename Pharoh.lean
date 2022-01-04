import Init.Control

namespace lambda

abbrev ℕ := Nat

inductive lambda (P N : Type) where
  | Var (_ : P)
  | App (f arg : lambda P N)
  | Abs (body : N → lambda P N)

open lambda

-- abbrev Term := ∀ {V P}, lambda V P

-- def lambda_id : Term := Abs (λ x => Var x)

-- def numVars_aux : lambda Unit → ℕ 
--   | Var _ => 1
--   | App f x => numVars_aux f + numVars_aux x
--   | Abs body => numVars_aux (body ())

-- abbrev numVars (e : Term) : ℕ := numVars_aux e

-- def canEta_aux2 : lambda Bool → Bool
--   | Var b => b
--   | App f x => canEta_aux2 f && canEta_aux2 x
--   | Abs body => canEta_aux2 (body true)

-- def canEta_aux
--   | Abs e' =>
--     match e' false with
--     | App e₁ (Var false) => canEta_aux2 e₁
--     | _ => false
--   | _ => false

-- abbrev canEta (e : Term) : Bool := canEta_aux e

-- abbrev Term1 := ∀ ⦃V⦄, V → lambda V

-- def subst {V} : lambda (lambda V) → lambda V
--   | Var e => e
--   | App f x => App (subst f) (subst x)
--   | Abs body => Abs (λ x => subst (body (Var x)))

-- abbrev Subst : Term1 → Term → Term :=
--   λ E₁ E₂ => subst (E₁ E₂) 

-- abbrev appV {V} (f x : V) : lambda V := App (Var f) (Var x)

-- def zero : Term := 
--   λ {V} => 
--     Abs (λ f : V => lambda_id)

-- def one : Term :=
--   λ {V} =>
--     Abs (λ f : V => Abs (λ x : V => appV f x))

-- def comp : Term :=
--   λ {V} =>
--     Abs (λ f : V => Abs (λ g : V => Abs (λ x : V => App (Var f) (appV g x))))

-- def add : Term :=
-- λ {V} =>
--     Abs (λ n : V => 
--     Abs (λ m : V => 
--     Abs (λ f : V => 
--       App (App comp (appV n f)) (appV m f)
--     )))

-- def mul : Term :=
-- λ {V} =>
--     Abs (λ n : V => 
--     Abs (λ m : V => 
--     Abs (λ f : V => 
--       App (Var n) (appV m f)
--     )))

-- def getF (V) : Term -> OptionT Id (lambda V -> lambda (lambda V)) :=
--   fun t =>
--   match @t (lambda V) with
--       | App (Abs f) _ => some f
--       | _ => none

-- def getCoArg (V) : lambda V -> OptionT Id (lambda V) :=
--   fun t =>
--   match t with
--       | App coArg _ => some coArg
--       | _ => none

-- def getArg (V) : lambda V -> OptionT Id (lambda V) :=
--   fun t =>
--   match t with
--       | App _ arg => some t
--       | _ => none

-- def beta' (t : Term) {V} : OptionT Id (lambda V) :=
--   do
--     let f <- getF V t
--     let arg <- getArg V t
--     pure (subst (f arg))

-- def beta_aux {α : Type} (default : α) : OptionT Id α → α 
--   | some a => a
--   | none => default

-- def do_beta (t : Term) : Term :=
--   λ {V} => beta_aux t (beta' t)

-- def app : Term → Term → Term :=
--   fun f x {V} => App f x

-- def two : Term := app (app add one) one

-- end lambda