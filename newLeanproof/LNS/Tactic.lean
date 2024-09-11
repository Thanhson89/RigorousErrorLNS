import LNS.Common
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

inductive RExpr where
  | Var
  | Const (c : ℝ)
  | Neg (a : RExpr)
  | Add (a : RExpr) (b : RExpr)
  | Sub (a : RExpr) (b : RExpr)
  | Mul (a : RExpr) (b : RExpr)
  | Div (a : RExpr) (b : RExpr)
  | Exp (a : RExpr)
  | Log (a : RExpr)
  -- | Logb (b : ℝ) (a : RExpr)
  -- | Expb (b : ℝ) (a : RExpr)
  | Pow (a : RExpr) (b : RExpr)

instance (n : ℕ) : OfNat RExpr n where ofNat := .Const n
instance : Neg RExpr where neg := .Neg
instance : Add RExpr where add := .Add
instance : Sub RExpr where sub := .Sub
instance : Mul RExpr where mul := .Mul
instance : Div RExpr where div := .Div
instance : Pow RExpr RExpr where pow := .Pow
instance : HPow RExpr ℕ RExpr where hPow a n := a ^ RExpr.Const n

@[simp]
def toFun : RExpr → ℝ → ℝ
  | .Var => fun x => x
  | .Const c => fun _ => c
  | .Neg a => fun x => -toFun a x
  | .Add a b => fun x => toFun a x + toFun b x
  | .Sub a b => fun x => toFun a x - toFun b x
  | .Mul a b => fun x => toFun a x * toFun b x
  | .Div a b => fun x => toFun a x / toFun b x
  | .Exp a => fun x => Real.exp (toFun a x)
  | .Log a => fun x => Real.log (toFun a x)
  -- | .Logb b a => fun x => Real.logb b (toFun a x)
  -- | .Expb b a => fun x => b ^ toFun a x
  | .Pow a b => fun x => toFun a x ^ toFun b x

def exprDeriv : RExpr → RExpr
  | .Var => .Const 1
  | .Const _ => .Const 0
  | .Neg a => -exprDeriv a
  | .Add a b => exprDeriv a + exprDeriv b
  | .Sub a b => exprDeriv a - exprDeriv b
  | .Mul a b => exprDeriv a * b + a * exprDeriv b
  | .Div a b => (exprDeriv a * b - a * exprDeriv b) / (b ^ 2)
  | .Exp a => .Exp a * exprDeriv a
  | .Log a => exprDeriv a / a
  -- | .Logb b a => .Div (exprDeriv a) (.Mul (.Const (Real.log b)) a)
  -- | .Expb b a => .Mul (.Mul (.Log (.Const b)) (exprDeriv a)) (.Expb b a)
  -- | .Pow a e => .Mul (.Mul (exprDeriv a) (.Const e)) (.Pow a (e - 1))
  | .Pow a b => exprDeriv a * b * a ^ (b - .Const 1) + exprDeriv b * a ^ b * .Log a

def sideConditions (e : RExpr) (x : ℝ) : List Prop :=
  match e with
  | .Var => []
  | .Const _ => []
  | .Neg a => sideConditions a x
  | .Add a b => sideConditions a x ++ sideConditions b x
  | .Sub a b => sideConditions a x ++ sideConditions b x
  | .Mul a b => sideConditions a x ++ sideConditions b x
  | .Div a b => (toFun b x ≠ 0) :: sideConditions a x ++ sideConditions b x
  | .Exp a => sideConditions a x
  | .Log a => (toFun a x ≠ 0) :: sideConditions a x
  -- | .Logb b a => (toFun a x ≠ 0) :: (b ≠ 0) :: sideConditions a x
  -- | .Expb b a => (b > 0) :: sideConditions a x
  -- | .Pow a e => (e ≥ 1) :: sideConditions a x
  | .Pow a b => (toFun a x > 0) :: sideConditions a x ++ sideConditions b x

lemma expr_hasDerivAt (e : RExpr) (x : ℝ) :
    (sideConditions e x).Forall id → HasDerivAt (toFun e) (toFun (exprDeriv e) x) x := by
  induction e with
  | Var =>
    simp [toFun, sideConditions];
    exact hasDerivAt_id' x
  | Const c =>
    simp [toFun, sideConditions]
    exact hasDerivAt_const x c
  | Neg a ha =>
    simp [toFun, sideConditions]
    intro h1
    exact HasDerivAt.neg (ha h1)
  | Add a b ha hb =>
    simp [toFun, sideConditions, List.forall_append]
    intro h1 h2
    apply HasDerivAt.add <;> tauto
  | Sub a b ha hb =>
    simp [toFun, sideConditions, List.forall_append]
    intro h1 h2
    apply HasDerivAt.sub <;> tauto
  | Mul a b ha hb =>
    simp [toFun, sideConditions, List.forall_append]
    intro h1 h2
    apply HasDerivAt.mul <;> tauto
  | Div a b ha hb =>
    simp [toFun, sideConditions, List.forall_append]
    intro h h1 h2
    apply HasDerivAt.div <;> tauto
  | Exp a =>
    simp [toFun, sideConditions]
    intro h1
    apply HasDerivAt.exp; tauto
  | Log a =>
    simp [toFun, sideConditions]
    intro h1 h2
    apply HasDerivAt.log <;> tauto
  -- | Expb b a ha =>
  --   simp [toFun, sideConditions]
  --   intro hb h1
  --   apply HasDerivAt.const_rpow <;> tauto
  -- | Pow a e ha =>
  --   simp [toFun, sideConditions]
  --   intro he h1
  --   apply HasDerivAt.rpow_const <;> tauto
  | Pow a b ha hb =>
    simp [toFun, sideConditions, List.forall_append]
    intro ha h1 h2
    apply HasDerivAt.rpow <;> tauto

lemma expr_diff_deriv_on (e : RExpr) (s : Set ℝ) (h : ∀ x ∈ s, (sideConditions e x).Forall id) :
    DifferentiableOn ℝ (toFun e) s ∧ ∀ x ∈ s, deriv (toFun e) x = toFun (exprDeriv e) x := by
  have H := expr_hasDerivAt e
  constructor <;> intro x xs
  · apply DifferentiableAt.differentiableWithinAt
    exact HasDerivAt.differentiableAt (H x $ h x xs)
  · exact HasDerivAt.deriv (H x $ h x xs)

lemma expr_diff_deriv (e : RExpr) (h : ∀ x, (sideConditions e x).Forall id) :
    Differentiable ℝ (toFun e) ∧ deriv (toFun e) = toFun (exprDeriv e) := by
  have ⟨hD, hd⟩ := expr_diff_deriv_on e Set.univ (fun x _ => h x)
  constructor
  · exact differentiableOn_univ.mp hD
  · exact funext fun x ↦ hd x trivial

open Lean Elab Command Term Meta Qq Tactic

-- #check Real.add
-- See Ring tactic implementation
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Cannot.20Find.20.60Real.2Eadd.60

partial def toRExpr (vars : Array Expr) (e : Expr) : MetaM Expr := do
  if ← isDefEq (vars.get! 0) e then
    return .const ``RExpr.Var []
  have e1 : Q(ℝ) := e
  let const := mkAppM ``RExpr.Const #[e]
  let Expr.const n _ := (← withReducible <| whnf e).getAppFn | const
  -- logInfo s!"n = {n}"
  match n with
  | ``Neg.neg => match e1 with
    | ~q(- $a) => mkAppM ``RExpr.Neg #[← toRExpr vars a]
  | ``HAdd.hAdd | ``Add.add => match e1 with
    | ~q($a + $b) => mkAppM ``RExpr.Add #[← toRExpr vars a, ← toRExpr vars b]
    | _ => const
  | ``HSub.hSub | ``Sub.sub => match e1 with
    | ~q($a - $b) => mkAppM ``RExpr.Sub #[← toRExpr vars a, ← toRExpr vars b]
    | _ => const
  | ``HMul.hMul | ``Mul.mul => match e1 with
    | ~q($a * $b) => mkAppM ``RExpr.Mul #[← toRExpr vars a, ← toRExpr vars b]
    | _ => const
  | ``HDiv.hDiv | ``Div.div => match e1 with
    | ~q($a / $b) => mkAppM ``RExpr.Div #[← toRExpr vars a, ← toRExpr vars b]
    | _ => const
  | ``Real.exp => match e1 with
    | ~q(Real.exp $a) => mkAppM ``RExpr.Exp #[← toRExpr vars a]
    | _ => const
  | ``Real.log => match e1 with
    | ~q(Real.log $a) => mkAppM ``RExpr.Log #[← toRExpr vars a]
    | _ => const
  | ``HPow.hPow | ``Pow.pow => match e1 with
    | ~q(($a : ℝ) ^ ($b : ℝ)) => mkAppM ``RExpr.Pow #[← toRExpr vars a, ← toRExpr vars b]
    | _ => const
  | _ => const

syntax deriv_at := (" at" <|> " within") term

elab "get_deriv" t:term loc:(deriv_at)? : tactic => do
  let realType := Expr.const ``Real []
  let realSetType ← mkAppM ``Set #[realType]
  withMainContext do
    let t ← Tactic.elabTerm t (some $ .forallE `x realType realType .default)
    let expr ← lambdaTelescope t (fun args e => toRExpr args e)
    let hyp := ← match loc with
                 | some loc => do
                    match loc with
                    | `(deriv_at| at $x) => do
                        let x ← Tactic.elabTerm x (some realType)
                        mkAppM ``expr_hasDerivAt #[expr, x]
                    | `(deriv_at| within $s) => do
                        let s ← Tactic.elabTerm s (some realSetType)
                        mkAppM ``expr_diff_deriv_on #[expr, s]
                    | _ => throwUnsupportedSyntax
                 | _ => mkAppM ``expr_diff_deriv #[expr]
    let hypType ← inferType hyp
    let (args, _, concl) ← forallMetaTelescope hypType
    liftMetaTactic fun mvarId => do
      let newId ← mvarId.assert `h concl (← mkAppM' hyp args)
      let (_, newId) ← newId.intro1P
      return args.toList.map Expr.mvarId! ++ [newId]
      --evalTactic (← `(tactic| simp [sideConditions, toFun] at *))


syntax "deriv_EQ " term: tactic

macro_rules
| `(tactic| deriv_EQ $t:term) =>
    `(tactic| get_deriv $t:term; simp; simp_all; ext x; try field_simp; ring_nf)

syntax "diff_fun " term: tactic

macro_rules
| `(tactic| diff_fun $t:term) =>
    `(tactic| get_deriv $t:term; simp; simp_all)
