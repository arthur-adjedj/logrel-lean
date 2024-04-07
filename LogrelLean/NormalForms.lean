import LogrelLean.Ast
import LogrelLean.Context
import LogrelLean.Weakening
import Std.CodeAction

open Term


inductive Whne : Term → Prop :=
  | tRel : Whne (tRel n)
  | tApp : Whne f → Whne (tApp f x)
  | tNatElim : Whne n → Whne (tNatElim P hz hs n)
  | tEmptyElim : Whne e → Whne (tEmptyElim P e)
  | tFst : Whne p → Whne (tFst p)
  | tSnd : Whne p → Whne (tSnd p)
  | tIdElim : Whne e → Whne (tIdElim A x P hr y e)

inductive Whnf : Term → Prop :=
  | tSort   : Whnf (tSort s)
  | tProd   : Whnf (tProd A B)
  | tLambda : Whnf (tLambda A B)
  | tNat    : Whnf tNat
  | tZero   : Whnf tZero
  | tSucc   : Whnf (tSucc n)
  | tEmpty  : Whnf tEmpty
  | tSig   : Whnf (tSig A B)
  | tPair : Whnf (tPair A B x y)
  | tId : Whnf (tId A x y)
  | tRefl : Whnf (tRefl A x)
  | ne : Whne n → Whnf n


def Whne.dec : (t : Term) → Decidable (Whne t) := fun
  | .tRel _ => .isTrue tRel
  | .tApp e _ => match dec e with
    | .isTrue h => .isTrue (tApp h)
    | .isFalse h => .isFalse (fun (tApp h') => h h')
  | .tNatElim _ _ _ e => match dec e with
    | .isTrue h => .isTrue (tNatElim h)
    | .isFalse h => .isFalse (fun (tNatElim h') => h h')
  | .tEmptyElim _ e => match dec e with
    | .isTrue h => .isTrue (tEmptyElim h)
    | .isFalse h => .isFalse (fun (tEmptyElim h') => h h')
  | .tIdElim _ _ _ _ _ e => match dec e with
    | .isTrue h => .isTrue (tIdElim h)
    | .isFalse h => .isFalse (fun (tIdElim h') => h h')
  | .tFst e => match dec e with
    | .isTrue h => .isTrue (tFst h)
    | .isFalse h => .isFalse (fun (tFst h') => h h')
  | .tSnd e => match dec e with
    | .isTrue h => .isTrue (tSnd h)
    | .isFalse h => .isFalse (fun (tSnd h') => h h')
  | .tSort _ | .tProd _ _ | .tLambda _ _
  | .tNat | .tZero | .tSucc _ | .tEmpty
  | .tSig _ _ | .tPair _ _ _ _ | .tId _ _ _
  | .tRefl _ _ => .isFalse nofun

instance : Decidable (Whne t) := Whne.dec _

def Whnf.dec : (t : Term) → Decidable (Whnf t) := fun
  | .tRel _ => .isTrue (.ne .tRel)
  | .tApp e _ => match Whne.dec e with
    | .isTrue h => .isTrue (.ne $ .tApp h)
    | .isFalse h => .isFalse (fun (.ne $ .tApp h') => h h')
  | .tNatElim _ _ _ e => match Whne.dec e with
    | .isTrue h => .isTrue (.ne $ .tNatElim h)
    | .isFalse h => .isFalse (fun (.ne $ .tNatElim h') => h h')
  | .tEmptyElim _ e => match Whne.dec e with
    | .isTrue h => .isTrue (.ne $ .tEmptyElim h)
    | .isFalse h => .isFalse (fun (.ne $ .tEmptyElim h') => h h')
  | .tIdElim _ _ _ _ _ e => match Whne.dec e with
    | .isTrue h => .isTrue (.ne $ .tIdElim h)
    | .isFalse h => .isFalse (fun (.ne $ .tIdElim h') => h h')
  | .tFst e => match Whne.dec e with
    | .isTrue h => .isTrue (.ne $ .tFst h)
    | .isFalse h => .isFalse (fun (.ne $ .tFst h') => h h')
  | .tSnd e => match Whne.dec e with
    | .isTrue h => .isTrue (.ne $ .tSnd h)
    | .isFalse h => .isFalse (fun (.ne $ .tSnd h') => h h')
  | .tSort _ => .isTrue .tSort
  | .tProd _ _  => .isTrue .tProd
  | .tLambda _ _ => .isTrue .tLambda
  | .tNat => .isTrue .tNat
  | .tZero => .isTrue .tZero
  | .tSucc _ => .isTrue .tSucc
  | .tEmpty => .isTrue .tEmpty
  | .tSig _ _ => .isTrue .tSig
  | .tPair _ _ _ _ => .isTrue .tPair
  | .tId _ _ _ => .isTrue .tId
  | .tRefl _ _ => .isTrue .tRefl

instance : Decidable (Whnf t) := Whnf.dec _
