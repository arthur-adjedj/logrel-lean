import LogrelLean.Ast
import LogrelLean.UntypedReduction
import LogrelLean.GenericTyping

def RedRel.{u, v} :=
  Ctx →
  Term →
  (Term → Type u) →
  (Term → Type u) →
  (Term → Term → Type u) →
  Type v

structure LRPack (Γ : Ctx) (A : Term) where
  eqTy  : Term → Type u
  redTm : Term → Type u
  eqTm  : Term → Term → Type u

notation "[ " P " | " Γ " ⊨ " A " ≃ " B " ]" => LRPack.eqTy Γ A P B
notation "[ " P " | " Γ " ⊨ " t " : " A " ]" => LRPack.redTm Γ A P t
notation "[ " P " | " Γ " ⊨ " t " ≃ " u " : " A " ]" => LRPack.eqTm Γ A P t u

def LRPack.adequate (R : RedRel) (P : LRPack Γ A) :=
  R Γ A P.eqTy P.redTm P.eqTm

structure LRAdequate (Γ : Ctx) (A : Term) (R : RedRel) where
  pack : LRPack Γ A
  adequate : pack.adequate R

instance : CoeOut (LRAdequate Γ A R) (LRPack Γ A) := ⟨LRAdequate.pack⟩
instance : CoeDep (LRAdequate Γ A R) lr (lr.pack.adequate R) := ⟨lr.adequate⟩

notation "[ " R " | " Γ " ⊨ " A " ]" => LRAdequate Γ A R
notation "[ " R " | " Γ " ⊨ " A " ≃ " B " | " RA " ]" => LRPack.eqTy (@LRAdequate.pack Γ A R RA) B
notation "[ " R " | " Γ " ⊨ " t " : " A " | " RA " ]" => LRPack.redTm (@LRAdequate.pack Γ A R RA) t
notation "[ " R " | " Γ " ⊨ " t " ≃ " u " : " A " | " RA " ]" => LRPack.eqTm (@LRAdequate.pack Γ A R RA) t u

inductive TypeLevel : Type :=
  | zero
  | one

inductive TypeLevel.Lt : TypeLevel → TypeLevel → Type
  | Oi : TypeLevel.Lt zero one

notation:60 A:60 "<<" B:60 => TypeLevel.Lt A B

variable [WfContext] [WfType] [ConvNeuConv] [RedType] [Typing] [ConvType] [RedTerm] [ConvTerm]

structure NeRedTy (Γ : Ctx) (A : Term) : Type where
  ty  : Term
  red : [ Γ ⊢ B :⤳*: ty]
  eq  : [ Γ ⊢ ty ~ ty : 𝒰]

notation "[ " Γ " ⊨ne " A " ]" => NeRedTy Γ A

structure NeRedTyEq (Γ : Ctx) (A B : Term) (neA : [ Γ ⊨ne A ]): Type where
  ty  : Term
  red : [ Γ ⊢ B :⤳*: ty]
  eq  : [ Γ ⊢ neA.ty ~ ty : 𝒰]

notation "[ " Γ " ⊨ne " A "≃" B "|" R" ]" => NeRedTyEq Γ A B R

structure NeRedTm (Γ : Ctx) (t A : Term) (neA : [ Γ ⊨ne A ]): Type where
  te : Term
  red :  [ Γ ⊢ t :⤳*: te : neA.ty ]
  eq :  [ Γ ⊢ t ~ t : neA.ty]

notation "[ " Γ " ⊨ne " t ":" A "|" R" ]" => NeRedTm Γ t A R


structure NeRedTmEq (Γ : Ctx) (t u A : Term) (neA : [ Γ ⊨ne A ]): Type where
  teL  : Term
  teR  : Term
  redL : [ Γ ⊢ t :⤳*: teL : neA.ty ]
  red  : [ Γ ⊢ u :⤳*: teR : neA.ty ]
  eq   : [ Γ ⊢ teL ~ teR  : neA.ty]

notation "[ " Γ " ⊨ne " t "≃" u ":" A "|" R" ]" => NeRedTmEq Γ t u A R

structure URedTy (l : TypeLevel) (Γ : Ctx) (A : Term) : Type where
  level : TypeLevel
  lt : level << l
  wfCtx : [ ⊢ Γ]
  red :  [ Γ ⊢ A :⤳*: 𝒰 ]

notation "[ " Γ " ⊨U⟨" l "⟩" A " ]" => URedTy l Γ A

structure URedTyEq (l : TypeLevel) (Γ : Ctx) (A : Term) : Type where
  red :  [ Γ ⊢ A :⤳*: 𝒰 ]

notation "[ " Γ " ⊨U≃" A " ]" => URedTyEq Γ A

structure URedTm (l : TypeLevel)
  (rec : ∀ {l'}, l' << l → RedRel) (Γ : Ctx) (t A : Term) (R: [ Γ ⊨U⟨l⟩ A ]) : Type _ where
  te : Term
  red : [ Γ ⊢ t :⤳*: te : 𝒰 ]
  --type : IsType te
  eqr : [ Γ ⊢ te ~ te : 𝒰]
  rel : [rec R.lt | Γ ⊨  t]

structure URedTmEq (l : TypeLevel)
  (rec : ∀ {l'}, l' << l → RedRel) (Γ : Ctx) (t u A : Term) (R: [ Γ ⊨U⟨l⟩ A ]) : Type _ where
  redL  : URedTm l rec Γ t A R
  redR  : URedTm l rec Γ u A R
  eq    : [ Γ ⊢ redL.te ≃ redR.te : 𝒰 ]
  relL  : [ rec R.lt | Γ ⊨ t ]
  relR  : [ rec R.lt | Γ ⊨ u ]
  relEq : [ rec R.lt | Γ ⊨ t ≃ u | relL ]

notation "[ " Rec "|" Γ " ⊨U" t ":" A "|" R " ]" => URedTm _ Rec Γ t A R
notation "[ " Rec "|" Γ " ⊨U" t "≃" u ":" A "|" R " ]" => URedTmEq _ Rec Γ t u A R
