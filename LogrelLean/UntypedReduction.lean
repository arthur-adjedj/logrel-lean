import LogrelLean.Ast
import LogrelLean.NormalForms
open Term

section

set_option hygiene false
local notation "[" t  "⤳" u "]" => OneRed t u
local notation "[" t  "⤳*" u "]" => RedClosure t u

-- @[aesop safe constructors]
inductive OneRed : Term → Term → Type := --Make live in Prop perhaps ?
  | bred: [ tApp (tLambda A t) a ⤳ t[a..]]
  | appSubst : [t ⤳ u] → [tApp t a ⤳ tApp u a]
  | natElim : [n ⤳ n'] → [tNatElim P hz hs n ⤳ tNatElim P hz hs n']
  | natElimZero :  [tNatElim P hz hs tZero ⤳ hz]
  | natElimSucc :  [tNatElim P hz hs (tSucc n) ⤳ tApp (tApp hs n) (tNatElim P hz hs n)]
  | emptyElimSubst : [e ⤳ e'] → [tEmptyElim P e ⤳ tEmptyElim P e']
  | fstSubst : [ p ⤳ p'] -> [ tFst p ⤳ tFst p']
  | fstPair  : [ tFst (tPair A B a b) ⤳ a ]
  | sndSubst : [ p ⤳ p'] -> [ tSnd p ⤳ tSnd p']
  | sndPair : [ tSnd (tPair A B a b) ⤳ b ]
  | idElimRefl : [ tIdElim A x P hr y (tRefl A' z) ⤳ hr ]
  | idElimSubst : [e ⤳ e'] -> [ tIdElim A x P hr y e ⤳ tIdElim A x P hr y e' ]


inductive RedClosure : Term → Term → Type :=
  | id : [t ⤳* t]
  | succ : [t ⤳ t'] → [t' ⤳* u] → [t ⤳* u]

end

set_option hygiene true
local notation "[" t  "⤳" u "]" => OneRed t u
local notation "[" t  "⤳*" u "]" => RedClosure t u

@[simp]
theorem Whne.noRed (h : Whne t) : [t ⤳ u] → False := by
  intro r
  induction r <;> cases h <;>
  first
    -- | aesop
    | sorry
    | next h => cases h

theorem Whnf.noRed (h : Whnf t) : [t ⤳ u] → False := by
  intro r
  induction r <;> cases h <;>
  (rename_i h
   cases h) <;>
  first
    | contradiction
    | apply Whne.noRed _ ‹_›
      assumption

theorem OneRed.inj : [t ⤳ u] → [t ⤳ v] → u = v := by
  intro h₁ h₂
  induction h₁ generalizing v <;> cases h₂ <;>
  first
    | rfl
    | contradiction
    | next ih _ h => rw [ih h]

theorem redWhne (h : Whne t): [t ⤳* u]  → t = u
  | .id => rfl
  | .succ bad _ => nomatch h.noRed bad

theorem redWhnf (h : Whnf t): [t ⤳* u]  → t = u
  | .id => rfl
  | .succ bad _ => nomatch h.noRed bad

def wh_red_red_det (h : Whnf u) : [t ⤳* u] -> [t ⤳* u'] -> [u' ⤳* u]
  | h,.id => h
  | .id,h => redWhnf ‹_› h ▸ .id
  | .succ h₁ h₂,.succ h₃ h₄ =>
    let .refl _ := OneRed.inj h₁ h₃
    wh_red_red_det h h₂ h₄
