import LogrelLean.Ast
import LogrelLean.Context
import LogrelLean.Weakening
open Term

section

set_option hygiene false
local notation "["   "⊢" Γ "]" => WfCtxDecl Γ
local notation "[" Γ "⊢" A "]" => WfTypeDecl Γ A
local notation "[" Γ "⊢" x ":" A "]" => TypingDecl Γ x A
local notation "[" Γ "⊢" A "≃" B "]" => ConvTypeDecl  Γ A B
local notation "[" Γ "⊢" x "≃" y ":" A "]" => ConvTermDecl Γ x y A
set_option quotPrecheck true

mutual
  inductive WfCtxDecl : Ctx → Type :=
    | nil  : [ ⊢ ε ]
    | cons :  [ Γ ⊢ A ] → [ ⊢ Γ,,A ]

  inductive WfTypeDecl : Ctx → Term → Type :=
    | U     : [ ⊢ Γ ]   → [ Γ ⊢ 𝒰 ]
    -- These can all be derived from `univ`, why are they a thing ?
    -- | nat   : [ ⊢ Γ ]   → [ Γ ⊢ tNat ]
    -- | empty : [ ⊢ Γ ]   → [ Γ ⊢ tEmpty ]
    -- | prod  : [ Γ ⊢ A ] → [ Γ,,A ⊢ B ]  → [ Γ ⊢ tProd A B ]
    -- | sig   : [ Γ ⊢ A ] → [ Γ,,A ⊢ B ]  → [ Γ ⊢ tSig A B ]
    -- | id    : [ Γ ⊢ A ] → [ Γ ⊢ x : A ] → [ Γ ⊢ y : A ] → [ Γ ⊢ tId A x y ]
    | univ  : [ Γ ⊢ A : 𝒰] → [ Γ ⊢ A ]

  inductive TypingDecl : Ctx → Term → Term → Type :=
    | var  : [ ⊢ Γ ] → InCtx Γ n A → [ Γ ⊢ tRel n : A ]
    | prod : [ Γ ⊢ A : 𝒰 ] → [ Γ,,A ⊢ B : 𝒰] → [ Γ ⊢ tProd A B : 𝒰]
    | lam  : [ Γ ⊢ A ] → [ Γ,,A ⊢ t : B ] → [ Γ ⊢ tLambda A t : tProd A B ]
    | app  : [ Γ ⊢ f : tProd A B ] → [ Γ ⊢ a : A ] → [ Γ ⊢ tApp f a : B[a..] ]
    | nat  : [ ⊢ Γ ] → [ Γ ⊢ tNat : 𝒰]
    | zero : [ ⊢ Γ ] → [ Γ ⊢ tzero : tNat]
    | succ : [ Γ ⊢ n : tNat]  → [ Γ ⊢ tSucc n : tNat]
    | natElim:
      [Γ,, tNat ⊢ P] →
      [Γ ⊢ hz : P[tZero..] ] →
      [Γ ⊢ hs : elimSuccHypTy P] →
      [Γ ⊢ n : tNat] → [Γ ⊢ tNatElim P hz hs n : P[n..]]
    | empty : [ ⊢ Γ ] → [ Γ ⊢ tEmpty : 𝒰]
    | emptyElim : [Γ,, tEmpty ⊢ P] → [Γ ⊢ e : tEmpty] → [Γ ⊢ tEmptyElim P e : P[e..]]
    | sig : [ Γ ⊢ A : 𝒰 ] → [ Γ,,A ⊢ B : 𝒰] → [ Γ ⊢ tSig A B : 𝒰]
    | pair : [ Γ ⊢ A ] → [ Γ,,A ⊢ B ] → [ Γ ⊢ a : A ] → [ Γ ⊢ b : B[a..]] →
      [ Γ ⊢ tPair A B a b : tSig A B]
    | fst :  [ Γ ⊢ p : tSig A B] →  [ Γ ⊢ tFst p :A]
    | snd :  [ Γ ⊢ p : tSig A B] →  [ Γ ⊢ tSnd p :B[(tFst p)..]]
    | id  :  [ Γ ⊢ A : 𝒰] → [ Γ ⊢ x : A ] → [ Γ ⊢ y : A ] → [ Γ ⊢ tId A x y : 𝒰]
    | refl : [ Γ ⊢ A ] → [ Γ ⊢ a : A ] → [ Γ ⊢ tRefl A a : tId A a a ]
    | idElim :
      [Γ ⊢ A] ->
      [Γ ⊢ x : A] ->
      [Γ ,, A ,, tId A⟨@wk₁ Γ A⟩ x⟨@wk₁ Γ A⟩ (tRel 0) ⊢ P] ->
      [Γ ⊢ hr : P[tRefl A x .: x..]] ->
      [Γ ⊢ y : A] ->
      [Γ ⊢ e : tId A x y] ->
      [Γ ⊢ tIdElim A x P hr y e : P[e .: y..]]
    | conv : [ Γ ⊢ t : A ] → [ Γ ⊢ A ≃ B ] → [ Γ ⊢ t : B ]
  inductive ConvTypeDecl : Ctx → Term → Term → Type :=
    | piCong  : [Γ ⊢ A] → [Γ ⊢ A ≃ B] → [Γ ,, A ⊢ C ≃ D] → [Γ ⊢ tProd A C ≃ tProd B D]
    | sigCong : [Γ ⊢ A] → [Γ ⊢ A ≃ B] → [Γ ,, A ⊢ C ≃ D] → [Γ ⊢ tSig A C ≃ tSig B D]
    | idCong  : [Γ ⊢ A ≃ A'] → [Γ ⊢ x ≃ x' : A] → [Γ ⊢ y ≃ y' : A] → [Γ ⊢ tId A x y ≃ tId A' x' y']
    | refl    : [Γ ⊢ A] → [Γ ⊢ A ≃ A]
    | symm    : [Γ ⊢ A ≃ B] → [Γ ⊢ B ≃ A]
    | trans   : [Γ ⊢ A ≃ B] → [Γ ⊢ B ≃ C] → [Γ ⊢ A ≃ C]
    | U       : [Γ ⊢ A ≃ A' : 𝒰] → [Γ ⊢ A ≃ A']
  /-- TODO add conv rule for Eta-/
  inductive ConvTermDecl : Ctx → Term → Term → Term → Type :=
    | bRed :
      [ Γ ⊢ A ] ->
      [ Γ ,, A ⊢ t : B ] ->
      [ Γ ⊢ a : A ] ->
      [ Γ ⊢ tApp (tLambda A t) a ≃ t[a..] : B[a..] ]
    | piCong :
      [ Γ ⊢ A : U] ->
      [ Γ ⊢ A ≃ B : U ] ->
      [ Γ ,, A ⊢ C ≃ D : U ] ->
      [ Γ ⊢ tProd A C ≃ tProd B D : U ]
    | sigCong :
      [ Γ ⊢ A : U] ->
      [ Γ ⊢ A ≃ B : U ] ->
      [ Γ ,, A ⊢ C ≃ D : U ] ->
      [ Γ ⊢ tSig A C ≃ tSig B D : U ]
    | appCong :
      [ Γ ⊢ f ≃ g : tProd A B ] ->
      [ Γ ⊢ a ≃ b : A ] ->
      [ Γ ⊢ tApp f a ≃ tApp g b : B[a..] ]
    | lambdaCong :
      [ Γ ⊢ A ] ->
      [ Γ ⊢ A ≃ A' ] ->
      [ Γ ⊢ A ≃ A'' ] ->
      [ Γ,, A ⊢ t ≃ u : B ] ->
      [ Γ ⊢ tLambda A' t ≃ tLambda A'' u : tProd A B ]
    -- | funEta :
    --   [ Γ ⊢ f : tProd A B ] ->
    --   [ Γ ⊢ tLambda A (eta_expand f) ≃ f : tProd A B ]

    | succCong :
      [Γ ⊢ n ≃ n' : tNat] ->
      [Γ ⊢ tSucc n ≃ tSucc n' : tNat]
    | natElimCong :
      [Γ ,, tNat ⊢ P ≃ P'] ->
      [Γ ⊢ hz ≃ hz' : P[tZero..]] ->
      [Γ ⊢ hs ≃ hs' : elimSuccHypTy P] ->
      [Γ ⊢ n ≃ n' : tNat] ->
      [Γ ⊢ tNatElim P hz hs n ≃ tNatElim P' hz' hs' n' : P[n..]]
    | natElimZero :
      [Γ ,, tNat ⊢ P ] ->
      [Γ ⊢ hz : P[tZero..]] ->
      [Γ ⊢ hs : elimSuccHypTy P] ->
      [Γ ⊢ tNatElim P hz hs tZero ≃ hz : P[tZero..]]
    | natElimSucc :
      [Γ ,, tNat ⊢ P ] ->
      [Γ ⊢ hz : P[tZero..]] ->
      [Γ ⊢ hs : elimSuccHypTy P] ->
      [Γ ⊢ n : tNat] ->
      [Γ ⊢ tNatElim P hz hs (tSucc n) ≃ tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]]

    | emptyElimCong :
      [Γ ,, tEmpty ⊢ P ≃ P'] ->
      [Γ ⊢ e ≃ e' : tEmpty] ->
      [Γ ⊢ tEmptyElim P e ≃ tEmptyElim P' e' : P[e..]]

    | pairCong:
      [Γ ⊢ A] ->
      [Γ ⊢ A ≃ A'] ->
      [Γ ⊢ A ≃ A''] ->
      [Γ,, A ⊢ B ≃ B'] ->
      [Γ,, A ⊢ B ≃ B''] ->
      [Γ ⊢ a ≃ a' : A] ->
      [Γ ⊢ b ≃ b' : B[a..]] ->
      [Γ ⊢ tPair A' B' a b ≃ tPair A'' B'' a' b' : tSig A B]
    | pairEta :
      [Γ ⊢ p : tSig A B] ->
      [Γ ⊢ tPair A B (tFst p) (tSnd p) ≃ p : tSig A B]
    | fstCong :
      [Γ ⊢ p ≃ p' : tSig A B] ->
      [Γ ⊢ tFst p ≃ tFst p' : A]
    | fstBeta :
      [Γ ⊢ A] ->
      [Γ ,, A ⊢ B] ->
      [Γ ⊢ a : A] ->
      [Γ ⊢ b : B[a..]] ->
      [Γ ⊢ tFst (tPair A B a b) ≃ a : A]
    | sndCong :
      [Γ ⊢ p ≃ p' : tSig A B] ->
      [Γ ⊢ tSnd p ≃ tSnd p' : B[(tFst p)..]]
    | sndBeta :
      [Γ ⊢ A] ->
      [Γ ,, A ⊢ B] ->
      [Γ ⊢ a : A] ->
      [Γ ⊢ b : B[a..]] ->
      [Γ ⊢ tSnd (tPair A B a b) ≃ b : B[(tFst (tPair A B a b))..]]

    | idCong :
      [Γ ⊢ A ≃ A' : U] ->
      [Γ ⊢ x ≃ x' : A] ->
      [Γ ⊢ y ≃ y' : A] ->
      [Γ ⊢ tId A x y ≃ tId A' x' y' : U ]
    | reflCong :
      [Γ ⊢ A ≃ A'] ->
      [Γ ⊢ x ≃ x' : A] ->
      [Γ ⊢ tRefl A x ≃ tRefl A' x' : tId A x x]
    | idElimCong :
      [Γ ⊢ A] ->
      [Γ ⊢ x : A] ->
      [Γ ⊢ A ≃ A'] ->
      [Γ ⊢ x ≃ x' : A] ->
      [Γ ,, A ,, tId A⟨@wk₁ Γ A⟩ x⟨@wk₁ Γ A⟩ (tRel 0) ⊢ P ≃ P'] ->
      [Γ ⊢ hr ≃ hr' : P[tRefl A x .: x..]] ->
      [Γ ⊢ y ≃ y' : A] ->
      [Γ ⊢ e ≃ e' : tId A x y] ->
      [Γ ⊢ tIdElim A x P hr y e ≃ tIdElim A' x' P' hr' y' e' : P[e .: y..]]
    | idElimRefl :
      [Γ ⊢ A] ->
      [Γ ⊢ x : A] ->
      [Γ ,, A ,, tId A⟨@wk₁ Γ A⟩ x⟨@wk₁ Γ A⟩ (tRel 0) ⊢ P] ->
      [Γ ⊢ hr : P[tRefl A x .: x..]] ->
      [Γ ⊢ y : A] ->
      [Γ ⊢ A'] ->
      [Γ ⊢ z : A] ->
      [Γ ⊢ A ≃ A'] ->
      [Γ ⊢ x ≃ y : A] ->
      [Γ ⊢ x ≃ z : A] ->
      [Γ ⊢ tIdElim A x P hr y (tRefl A' z) ≃ hr : P[tRefl A' z .: y..]]
    | refl    : [Γ ⊢ x : A] → [Γ ⊢ x ≃ x : A]
    | symm    : [Γ ⊢ x ≃ y : A] → [Γ ⊢ y ≃ x : A]
    | trans   : [Γ ⊢ x ≃ y : A] → [Γ ⊢ y ≃ z  : A] → [Γ ⊢ x ≃ z : A]
    | conv    : [Γ ⊢ x ≃ y : A] → [Γ ⊢ A ≃ B] → [Γ ⊢ x ≃ y : B]

end

end

notation "[" "⊢" Γ "]" => WfCtxDecl Γ
notation "[" Γ "⊢" A "]" => WfTypeDecl Γ A
notation "[" Γ "⊢" x ":" A "]" => TypingDecl Γ x A
notation "[" Γ "⊢" A "≃" B "]" => ConvTypeDecl  Γ A B
notation "[" Γ "⊢" x ":" A "≃" B "]" => ConvTermDecl x Γ A B
