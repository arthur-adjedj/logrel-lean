import LogrelLean.Ast
import LogrelLean.UntypedReduction
import LogrelLean.GenericTyping
import LogrelLean.Relation

open Term

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

notation "[ " P " | " Γ " ⊨ " A " ≃ " B " ]" => @LRPack.eqTy Γ A P B
notation "[ " P " | " Γ " ⊨ " t " : " A " ]" => @LRPack.redTm Γ A P t
notation "[ " P " | " Γ " ⊨ " t " ≃ " u " : " A " ]" => @LRPack.eqTm Γ A P t u

def LRPack.Adequate (R : RedRel) (P : LRPack Γ A) :=
  R Γ A P.eqTy P.redTm P.eqTm

structure LRAdequate (Γ : Ctx) (A : Term) (R : RedRel) where
  pack : LRPack Γ A
  adequate : pack.Adequate R

instance : CoeOut (LRAdequate Γ A R) (LRPack Γ A) := ⟨LRAdequate.pack⟩
instance : CoeDep (LRAdequate Γ A R) lr (lr.pack.Adequate R) := ⟨lr.adequate⟩

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

structure NeRedTy (Γ : Ctx) (A : Term) : Type u where
  ty  : Term
  red : [ Γ ⊢ B :⤳*: ty]
  eq  : [ Γ ⊢ ty ~ ty : 𝒰]

notation "[ " Γ " ⊨ne " A " ]" => NeRedTy Γ A

structure NeRedTyEq (Γ : Ctx) (A B : Term) (neA : [ Γ ⊨ne A ]): Type u where
  ty  : Term
  red : [ Γ ⊢ B :⤳*: ty]
  eq  : [ Γ ⊢ neA.ty ~ ty : 𝒰]

notation "[ " Γ " ⊨ne " A "≃" B "|" R" ]" => NeRedTyEq Γ A B R

structure NeRedTm (Γ : Ctx) (t A : Term) (neA : [ Γ ⊨ne A ]): Type u where
  te : Term
  red :  [ Γ ⊢ t :⤳*: te : neA.ty ]
  eq :  [ Γ ⊢ t ~ t : neA.ty]

notation "[ " Γ " ⊨ne " t ":" A "|" R" ]" => NeRedTm Γ t A R


structure NeRedTmEq (Γ : Ctx) (t u A : Term) (neA : [ Γ ⊨ne A ]): Type u where
  teL  : Term
  teR  : Term
  redL : [ Γ ⊢ t :⤳*: teL : neA.ty ]
  red  : [ Γ ⊢ u :⤳*: teR : neA.ty ]
  eq   : [ Γ ⊢ teL ~ teR  : neA.ty]

notation "[ " Γ " ⊨ne " t "≃" u ":" A "|" R" ]" => NeRedTmEq Γ t u A R

structure URedTy (l : TypeLevel) (Γ : Ctx) (A : Term) : Type u where
  level : TypeLevel
  lt : level << l
  wfCtx : [ ⊢ Γ]
  red :  [ Γ ⊢ A :⤳*: 𝒰 ]

notation "[ " Γ " ⊨U⟨" l "⟩" A " ]" => URedTy l Γ A

structure URedTyEq (Γ : Ctx) (A : Term) : Type u where
  red :  [ Γ ⊢ A :⤳*: 𝒰 ]

notation "[ " Γ " ⊨U≃" A " ]" => URedTyEq Γ A

structure URedTm (l : TypeLevel)
  (rec : ∀ {l'}, l' << l → RedRel) (Γ : Ctx) (t A : Term) (R: [ Γ ⊨U⟨l⟩ A ]) where
  te : Term
  red : [ Γ ⊢ t :⤳*: te : 𝒰 ]
  --type : IsType te
  eqr : [ Γ ⊢ te ~ te : 𝒰]
  rel : [rec R.lt | Γ ⊨  t]

structure URedTmEq (l : TypeLevel)
  (rec : ∀ {l'}, l' << l → RedRel) (Γ : Ctx) (t u A : Term) (R: [ Γ ⊨U⟨l⟩ A ]) where
  redL  : URedTm l rec Γ t A R
  redR  : URedTm l rec Γ u A R
  eq    : [ Γ ⊢ redL.te ≃ redR.te : 𝒰 ]
  relL  : [ rec R.lt | Γ ⊨ t ]
  relR  : [ rec R.lt | Γ ⊨ u ]
  relEq : [ rec R.lt | Γ ⊨ t ≃ u | relL ]

notation "[ " Rec "|" Γ " ⊨U" t ":" A "|" R " ]" => URedTm _ Rec Γ t A R
notation "[ " Rec "|" Γ " ⊨U" t "≃" u ":" A "|" R " ]" => URedTmEq _ Rec Γ t u A R

structure PolyRedPack (Γ : Ctx) (A B: Term) where
  ATy  : [ Γ ⊢ A]
  BTy  : [ Γ ⊢ B]
  ARed (ρ : Δ ≤ Γ) (h: [⊢ Δ]) : LRPack Δ A⟨ρ⟩
  BRed (ρ : Δ ≤ Γ) (h: [⊢ Δ]) :
    [ ARed ρ h | Δ ⊨ a : A⟨ρ⟩] → LRPack Δ B[a .: (.tRel ∘ ρ)]
  BExt (ρ : Δ ≤ Γ) (h: [⊢ Δ]) (ha : [ ARed ρ h | Δ ⊨ a : A⟨ρ⟩]) :
    [ ARed ρ h | Δ ⊨ b : A⟨ρ⟩] →
    [ ARed ρ h | Δ ⊨ a ≃ b : A⟨ρ⟩] →
    [ BRed ρ h ha | Δ ⊨ B[a .: (.tRel ∘ ρ)] ≃ B[b .: (.tRel ∘ ρ)]]

structure PolyRedPackAdequate {Γ : Ctx} (R : RedRel) (PA : PolyRedPack Γ A B) where
  AAd (ρ : Δ ≤ Γ) (h: [⊢ Δ]) :
    (PA.ARed ρ h).Adequate R
  BAd (ρ : Δ ≤ Γ) (h: [⊢ Δ]) (ha : [ PA.ARed ρ h | Δ ⊨ a : A⟨ρ⟩]) :
    (PA.BRed ρ h ha).Adequate R

structure PolyRedEq {Γ : Ctx} {A B : Term} (PA : PolyRedPack Γ A B) (A' B' : Term) where
  ARed (ρ : Δ ≤ Γ) (h: [⊢ Δ]) :
    [ PA.ARed ρ h | Δ ⊨ A⟨ρ⟩ ≃ A'⟨ρ⟩ ]
  BRed (ρ : Δ ≤ Γ) (h: [⊢ Δ]) (ha : [ PA.ARed ρ h | Δ ⊨ a : A⟨ρ⟩]) :
  [ PA.BRed ρ h ha | Δ ⊨ B[a .: (.tRel ∘ ρ)] ≃ B'[a .: (.tRel ∘ ρ)] ]

structure ParamRedTyPack (T : Term → Term → Term) (Γ : Ctx)  (A : Term) where
  dom     : Term
  cod     : Term
  out_ty := T dom cod
  red     : [Γ ⊢ A :⤳*: T dom cod]
  eq_dom  : [Γ ⊢ dom ≃ dom]
  eq      : [Γ ⊢ T dom cod ≃ T dom cod]
  polyRed : PolyRedPack Γ dom cod

instance : CoeDep (ParamRedTyPack T Γ A) pk (PolyRedPack Γ pk.dom pk.cod):= ⟨pk.polyRed⟩

structure ParamRedTyEq {T : Term → Term → Term} {Γ : Ctx}  {A: Term} (B: Term) (PiA : ParamRedTyPack T Γ A) : Type _  where
  dom : Term
  cod : Term
  red : [Γ ⊢ B :⤳*: T dom cod ]
  eq_dom : [Γ ⊢ PiA.dom ≃ dom]
  eq : [Γ ⊢ T PiA.dom PiA.cod ≃ T dom cod]
  polyRed : PolyRedEq PiA.polyRed dom cod


def PiRedTy := ParamRedTyPack .tProd

def PiRedTyAdequate (R : RedRel) (PiA : ParamRedTyPack T Γ A) := PolyRedPackAdequate R PiA.polyRed

def PiRedTyEq {A : Term} (PiA : PiRedTy Γ A) (B : Term) :=
  ParamRedTyEq B PiA

notation "[ " Γ " ⊨Πd" A " ]" => PiRedTy Γ A
notation "[" Γ "⊨Π" A "≃" B "|" PiA "]" => PiRedTyEq (Γ:= Γ) (A:= A) PiA B

inductive isLRFun (PiA : PiRedTy Γ A) : Term → Type _ :=
  | lam (A' t) :
    (∀ {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]) (domRed:= PiA.polyRed.ARed ρ h),
      [domRed | Δ ⊨ PiA.dom⟨ρ⟩ ≃ A'⟨ρ⟩]) →
    (∀ {Δ a} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ])
      (ha : [ PiA.polyRed.ARed ρ h | Δ ⊨ a : PiA.dom⟨ρ⟩ ]),
        [PiA.polyRed.BRed ρ h ha | Δ ⊨ t[a .: (.tRel ∘ ρ)] : PiA.cod[a .: (.tRel ∘ ρ)]]) →
    isLRFun PiA (.tLambda A' t)
  | NeLRFun (f): [Γ ⊢ f ~ f : .tProd PiA.dom PiA.cod] → isLRFun PiA f


structure PiRedTm (t : Term) (PiA : PiRedTy Γ A) where
  nf    : Term
  red   : [ Γ ⊢ t :⤳*: nf : .tProd PiA.dom PiA.cod ]
  isfun : isLRFun PiA nf
  refl  : [ Γ ⊢ nf ≃ nf : .tProd PiA.dom PiA.cod ]
  app {Δ a} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ])
     (ha : [ PiA.polyRed.ARed ρ h | Δ ⊨ a : PiA.dom⟨ρ⟩ ])
     : [PiA.polyRed.BRed ρ h ha | Δ ⊨ .tApp nf⟨ρ⟩ a : PiA.cod[a .: (.tRel ∘ ρ)]]
  eq {Δ a b} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ])
      (ha : [ PiA.polyRed.ARed ρ h | Δ ⊨ a : PiA.dom⟨ρ⟩ ])
      (hb : [ PiA.polyRed.ARed ρ h | Δ ⊨ b : PiA.dom⟨ρ⟩ ])
      (eq : [ PiA.polyRed.ARed ρ h | Δ ⊨ a ≃ b : PiA.dom⟨ρ⟩ ])
      : [ PiA.polyRed.BRed ρ h ha | Δ ⊨ .tApp nf⟨ρ⟩ a ≃ .tApp nf⟨ρ⟩ b : PiA.cod[a .: (.tRel ∘ ρ)] ]

notation "[" Γ "⊨Π" t ":" A "|" PiA "]" => PiRedTm (Γ:= Γ) (A:=A) t PiA

structure PiRedTmEq {t u A : Term} {PiA : PiRedTy Γ A} where
redL : [ Γ ⊨Π t : A | PiA ]
redR : [ Γ ⊨Π u : A | PiA ]
eq : [ Γ ⊢ redL.nf ≃ redR.nf : .tProd PiA.dom PiA.cod ]
eqApp {Δ a} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ])
  (ha : [PiA.polyRed.ARed ρ h | Δ ⊨ a : PiA.dom⟨ρ⟩ ] )
  : [ PiA.polyRed.BRed ρ h ha | Δ ⊨
      .tApp redL.nf⟨ρ⟩ a ≃ .tApp redR.nf⟨ρ⟩ a : PiA.cod[a .: (.tRel ∘ ρ)]]

notation "[" Γ "⊨Π" t "≃" u ":" A "|" PiA "]" => PiRedTmEq (Γ:= Γ) (t:=t) (u:=u) (A:=A) (PiA:=PiA)



def SigRedTy := ParamRedTyPack .tSig

def SigRedTyAdequate (R : RedRel) (SigA : ParamRedTyPack T Γ A) := PolyRedPackAdequate R SigA.polyRed

def SigRedTyEq {A : Term} (SigA : SigRedTy Γ A) (B : Term) :=
  ParamRedTyEq B SigA

notation "[ " Γ " ⊨Σd" A " ]" => SigRedTy Γ A
notation "[" Γ "⊨Σ" A "≃" B "|" SigA "]" => SigRedTyEq (Γ:= Γ) (A:= A) SigA B

inductive isLRPair (SigA : SigRedTy Γ A) : Term → Type _
  | PairLRpair (A' B' a b : Term)
    (rdom : ∀ {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]),
        [ SigA.polyRed.ARed ρ h | Δ ⊨ SigA.dom⟨ρ⟩ ≃ A'⟨ρ⟩ ])
    (rcod : ∀ {Δ a} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ])
      (ha : [ SigA.polyRed.ARed ρ h | Δ ⊨ a : SigA.dom⟨ρ⟩ ]),
        [SigA.polyRed.BRed ρ h ha | Δ ⊨ SigA.cod[a .: (.tRel ∘ ρ)] ≃ B'[a .: (.tRel ∘ ρ)]])
    (rfst : ∀ {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]),
        [SigA.polyRed.ARed ρ h | Δ ⊨ a⟨ρ⟩ : SigA.dom⟨ρ⟩])
    (rsnd : ∀ {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]),
        [SigA.polyRed.BRed ρ h (rfst ρ h) | Δ ⊨ b⟨ρ⟩ : SigA.cod[a⟨ρ⟩ .: (.tRel ∘ ρ)] ]) :
    isLRPair SigA (.tPair A' B' a b)

  | NeLRPair : ∀ p : Term, [Γ ⊢ p ~ p : .tSig SigA.dom SigA.cod] → isLRPair SigA p


structure SigRedTm (SigA : SigRedTy Γ A) (t: Term) where
  nf    : Term
  red : [ Γ ⊢ t :⤳*: nf : SigA.out_ty ]
  ispair : isLRPair SigA nf
  refl : [ Γ ⊢ nf ≃ nf : SigA.out_ty ]
  fstRed {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]) :
    [SigA.polyRed.ARed ρ h | Δ ⊨ .tFst nf⟨ρ⟩ : SigA.dom⟨ρ⟩]
  sndRed  {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]) :
    [SigA.polyRed.BRed ρ h (fstRed ρ h) | Δ ⊨ .tSnd nf⟨ρ⟩ : _]

notation "[" Γ "⊨Σ" u ":" A "|" SigA "]" => SigRedTm (Γ:= Γ) (A:=A) SigA u

structure SigRedTmEq {A : Term} (SigA : SigRedTy Γ A) (t u : Term) where
  redL : [ Γ ⊨Σ t : A | SigA ]
  redR : [ Γ ⊨Σ u : A | SigA ]
  eq : [ Γ ⊢ redL.nf ≃ redR.nf : SigA.out_ty ]
  eqFst {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]) :
    [SigA.polyRed.ARed ρ h | Δ ⊨ .tFst redL.nf⟨ρ⟩ ≃ .tFst redR.nf⟨ρ⟩ : SigA.dom⟨ρ⟩]
  eqSnd {Δ} (ρ : Δ ≤ Γ) (h : [ ⊢ Δ ]) (redfstL := redL.fstRed ρ h) :
    [SigA.polyRed.BRed ρ h redfstL | Δ ⊨ .tSnd redL.nf⟨ρ⟩ ≃ .tSnd redR.nf⟨ρ⟩ : _]

notation "[" Γ " ⊨Σ " t " ≃ " u " : " A " | " SigA "]" => SigRedTmEq (Γ:= Γ) (A:=A) t SigA t u


structure RedTm (Γ : Ctx) (k A : Term) : Type u where
    ty : [Γ ⊢ k : A]
    refl : [Γ ⊢ k ~ k : A]

structure RedTmEq (Γ : Ctx) (k l A : Term) : Type u where
    conv : [Γ ⊢ k ~ l : A]

notation "[" Γ " ⊨NeNf " k " : " A "]" => RedTm Γ k A
notation "[" Γ " ⊨NeNf " k " ≃ " l " : " A "]" => RedTmEq Γ k l A

-- Reducibility of natural number type


structure NatRedTy (Γ : Ctx) (A : Term) : Type u where
  red : [Γ ⊢ A :⤳*: tNat]

notation "[" Γ " ⊨ℕ " A "]" => NatRedTy Γ A

structure NatRedTyEq {Γ : Ctx} {A : Term} (NA : NatRedTy Γ A) (B : Term) : Type u where
  red : [Γ ⊢ B :⤳*: tNat]



notation "[" Γ " ⊨ℕ " A " ≃ " B " | " RA "]" => NatRedTyEq (Γ:=Γ) (A:=A) RA B


mutual
  inductive NatRedTm {Γ : Ctx} {A: Term} (NA : NatRedTy Γ A) : Term → Type u :=
  | Build_NatRedTm {t}
    (nf : Term)
    (red : [Γ ⊢ t :⤳*: nf : .tNat ])
    (eq : [Γ ⊢ nf ≃ nf : .tNat])
    (prop : NatProp (NA:=NA) nf) : NatRedTm NA t

  inductive NatProp {Γ : Ctx} {A: Term} (NA : NatRedTy Γ A) : Term → Type u :=
  | zeroR  : NatProp NA tZero
  | succR {n} :
    NatRedTm NA n →
    NatProp NA (.tSucc n)
  | neR {ne} : [Γ ⊨NeNf ne : tNat] → NatProp NA ne
end

-- Let _NatRedInductionType :=
--   ltac:(let ind := fresh "ind" in
--       pose (ind := _NatRedInduction)
--       let ind_ty := type of ind in
--       exact ind_ty).

-- Let NatRedInductionType :=
--   ltac: (let ind := eval cbv delta [_NatRedInductionType] zeta
--     in _NatRedInductionType in
--     let ind' := polymorphise ind in
--   exact ind').

-- KM: looks like there is a bunch of polymorphic universes appearing there...


def NatRedTm.nf {Γ A n} {NA : [Γ ⊨ℕ A]} : NatRedTm (NA:=NA) n → Term :=
  fun ⟨nf,_,_,_⟩ => nf


def NatRedTm.red {Γ A n} {NA : [Γ ⊨ℕ A]} : (Rn : NatRedTm (NA:=NA) n) → [Γ ⊢ n :⤳*: nf Rn : .tNat] :=
  fun ⟨_,red,_,_⟩ => red

notation "[" Γ " ⊨ℕ " t  " : " A " | " NA "]" => NatRedTm (Γ:=Γ) (A:=A) (NA:=NA) t

mutual

  inductive NatRedTmEq {Γ : Ctx} {A: Term} (NA : NatRedTy Γ A) : Term → Term → Type u :=
  | Build_NatRedTmEq {t u}
    (nfL nfR : Term)
    (redL : [Γ ⊢ t :⤳*: nfL : tNat])
    (redR : [Γ ⊢ u :⤳*: nfR : tNat ])
    (eq : [Γ ⊢ nfL ≃ nfR : tNat])
    (prop : NatPropEq (NA:=NA) nfL nfR) : NatRedTmEq NA t u

  inductive NatPropEq {Γ : Ctx} {A: Term} (NA : NatRedTy Γ A) : Term → Term → Type u :=
  | zeroReq :
    NatPropEq NA tZero tZero
  | succReq {n n'} :
    NatRedTmEq NA n n' →
    NatPropEq NA (tSucc n) (tSucc n')
  | neReq {ne ne'} : [Γ ⊨NeNf ne ≃ ne' : tNat] → NatPropEq NA ne ne'

end

notation "[" Γ " ⊨ℕ " t " ≃ " u " : " A " | " NA "]" => NatRedTmEq (Γ:=Γ) (A:=A) (NA:=NA) t u

-- Reducibility of empty type
structure EmptyRedTy (Γ : Ctx) (A : Term) : Type where
  red : [Γ ⊢ A :⤳*: tEmpty]

notation "[" Γ " ⊨⊥ " A "]" => EmptyRedTy Γ A


structure EmptyRedTyEq {Γ : Ctx} {A : Term} (NA : EmptyRedTy Γ A) (B : Term) : Type u where
  red : [Γ ⊢ B :⤳*: tEmpty]

notation "[" Γ " ⊨⊥ " A " ≃ " B" | " NA "]" => EmptyRedTyEq (Γ:=Γ) (A:=A) (NA:=NA) B


inductive EmptyProp {Γ : Ctx} : Term → Type u :=
  | neR {ne} : [Γ ⊨NeNf ne : tEmpty] → EmptyProp ne

structure EmptyRedTm {Γ : Ctx} {A: Term} (NA : EmptyRedTy Γ A) (t: Term) where
  nf   : Term
  red  : [Γ ⊢ t :⤳*: nf : tEmpty ]
  eq   : [Γ ⊢ nf ≃ nf : tEmpty]
  prop : EmptyProp (Γ:=Γ) nf

notation "[" Γ " ⊨⊥ " t " : " A " | " NA "]" => EmptyRedTm (Γ:=Γ) (A:=A) (NA:=NA) t

inductive EmptyPropEq {Γ : Ctx} : Term → Term → Type u :=
  | neReq {ne ne'} : [Γ ⊨NeNf ne ≃ ne' : tEmpty] → EmptyPropEq ne ne'

structure EmptyRedTmEq {Γ : Ctx} {A: Term} (NA : EmptyRedTy Γ A) (t u:Term) where
  nfL  : Term
  nfR  : Term
  redL : [Γ ⊢ t :⤳*: nfL : tEmpty]
  redR : [Γ ⊢ u :⤳*: nfR : tEmpty ]
  eq   : [Γ ⊢ nfL ≃ nfR : tEmpty]
  prop : EmptyPropEq (Γ:=Γ) nfL nfR


notation "[" Γ " ⊨⊥ " t " ≃ " u " : " A " | " NA "]" => EmptyRedTmEq (Γ:=Γ) (A:=A) (NA:=NA) t u


-- Logical relation for Identity types

structure IdRedTyPack (Γ : Ctx) (A : Term) where
  ty : Term
  lhs : Term
  rhs : Term
  out_ty := tId ty lhs rhs
  red : [Γ ⊢ A :⤳*: out_ty]
  eq : [Γ ⊢ out_ty ≃ out_ty]
  tyRed : LRPack Γ ty
  lhsRed : [ tyRed | Γ ⊨ lhs : _ ]
  rhsRed : [ tyRed | Γ ⊨ rhs : _ ]
  /--Bake in PER property for reducible conversion at ty  to cut dependency cycles -/
  lhsRedRefl : [ tyRed | Γ ⊨ lhs ≃ lhs : _ ]
  rhsRedRefl : [ tyRed | Γ ⊨ rhs ≃ rhs : _ ]
  tyPER : PER (fun t u => [tyRed | _ ⊨ t ≃ u : _])
  tyKripke : ∀ {Δ} (ρ : Δ ≤ Γ) (_wfΔ : [⊢Δ]), LRPack Δ ty⟨ρ⟩
  tyKripkeEq : ∀ {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [⊢Δ]) (wfΞ : [⊢Ξ]) B,
    ρ' = ρ'' ∘w ρ → [tyKripke ρ wfΔ | _ ⊨ _ ≃ B] → [tyKripke ρ' wfΞ | _ ⊨ _ ≃ B⟨ρ''⟩]
  tyKripkeTm : ∀ {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [⊢Δ]) (wfΞ : [⊢Ξ]) t,
    ρ' = ρ'' ∘w ρ → [tyKripke ρ wfΔ | _ ⊨ t : _] → [tyKripke ρ' wfΞ | _ ⊨ t⟨ρ''⟩ : _]
  tyKripkeTmEq : ∀ {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [⊢Δ]) (wfΞ : [⊢Ξ]) t u,
    ρ' = ρ'' ∘w ρ → [tyKripke ρ wfΔ | _ ⊨ t ≃ u : _] → [tyKripke ρ' wfΞ | _ ⊨ t⟨ρ''⟩ ≃ u⟨ρ''⟩ : _]

structure IdRedTyAdequate
  {Γ : Ctx} {A : Term} (R : RedRel) (IA : IdRedTyPack Γ A) where
  tyAd : IA.tyRed.Adequate R
  tyKripkeAd : ∀ {Δ} (ρ : Δ ≤ Γ) (wfΔ : [⊢Δ]), (IA.tyKripke ρ wfΔ).Adequate R

structure IdRedTyEq
  {Γ : Ctx} {A : Term} (IA : IdRedTyPack Γ A) (B : Term) where
  ty : Term
  lhs : Term
  rhs : Term
  out_ty := tId ty lhs rhs
  red : [Γ ⊢ B :⤳*: out_ty]
  eq : [Γ ⊢ IA.out_ty ≃ out_ty]
  tyRed0 := IA.tyRed
  tyRed : [ tyRed0 | _ ⊨ _ ≃ ty ]
  -- lhsConv : [ Γ ⊢ IA.(IdRedTyPack.lhs) ≃ lhs : IA.(IdRedTyPack.ty) ]
  -- rhsConv : [ Γ ⊢ IA.(IdRedTyPack.rhs) ≃ rhs : IA.(IdRedTyPack.ty) ]
  lhsRed : [ tyRed0 | _ ⊨ IA.lhs ≃ lhs : _ ]
  rhsRed : [ tyRed0 | _ ⊨ IA.rhs ≃ rhs : _ ]

inductive IdProp {Γ : Ctx} {A: Term} (IA : IdRedTyPack Γ A) : Term → Type _ :=
  | reflR {A x} :
    [Γ ⊢ A] →
    [Γ ⊢ x : A] →
    [IA.tyRed | _ ⊨ _ ≃ A] →
    [IA.tyRed | _ ⊨ IA.lhs ≃ x : _ ] →
    --  Should the index only be conversion ?
    [IA.tyRed | _ ⊨ IA.rhs ≃ x : _ ] →
    IdProp IA (tRefl A x)
  | neR {ne} : [Γ ⊨NeNf ne : IA.out_ty] → IdProp IA ne

structure IdRedTm {Γ : Ctx} {A: Term} (IA : IdRedTyPack Γ A) (t : Term) where
    nf : Term
    red : [Γ ⊢ t :⤳*: nf : IA.out_ty ]
    eq : [Γ ⊢ nf ≃ nf : IA.out_ty]
    prop : IdProp (Γ:=Γ) (A:=A) (IA:=IA) nf



inductive IdPropEq {Γ : Ctx} {A: Term} {IA : IdRedTyPack Γ A} : Term → Term → Type _ :=
  | reflReq {A A' x x'} :
    [Γ ⊢ A] →
    [Γ ⊢ A'] →
    [Γ ⊢ x : A] →
    [Γ ⊢ x' : A'] →
    [IA.tyRed | _ ⊨ _ ≃ A] →
    [IA.tyRed | _ ⊨ _ ≃ A'] →
    [IA.tyRed | _ ⊨ IA.lhs ≃ x : _ ] →
    [IA.tyRed | _ ⊨ IA.lhs ≃ x' : _ ] →
    -- Should the indices only be conversion ?
    [IA.tyRed | _ ⊨ IA.rhs ≃ x : _ ] →
    [IA.tyRed | _ ⊨ IA.rhs ≃ x' : _ ] →
    IdPropEq (tRefl A x) (tRefl A' x')
  | neReq {ne ne'} : [Γ ⊨NeNf ne ≃ ne' : IA.out_ty] → IdPropEq ne ne'

  structure IdRedTmEq {Γ : Ctx} {A: Term} (IA : IdRedTyPack Γ A) (t u : Term) where
      nfL : Term
      nfR : Term
      redL : [Γ ⊢ t :⤳*: nfL : IA.out_ty ]
      redR : [Γ ⊢ u :⤳*: nfR : IA.out_ty ]
      eq : [Γ ⊢ nfL ≃ nfR : IA.out_ty]
      prop : IdPropEq (Γ:=Γ) (A:=A) (IA:=IA) nfL nfR

/--Definition of the logical relation-/
inductive LR
  [WfContext] [WfType] [Typing] [ConvTerm] [ConvType] [ConvNeuConv] [RedType] [RedTerm]
  {l : TypeLevel} (rec : ∀ l', l' << l → RedRel)
: RedRel :=
  | LRU {Γ A} (H : [Γ ⊨U⟨l⟩ A]) :
      LR rec Γ A
      (fun B   => [Γ ⊨U≃ B ])
      (fun t   => [ rec _ | Γ ⊨U t     : A | H ])
      (fun t u => [ rec _ | Γ ⊨U t ≃ u : A | H ])
  | LRne {Γ A} (neA : [ Γ ⊨ne A ]) :
      LR rec Γ A
      (fun B   =>  [ Γ ⊨ne A ≃ B     | neA])
      (fun t   =>  [ Γ ⊨ne t     : A | neA])
      (fun t u =>  [ Γ ⊨ne t ≃ u : A | neA])
  | LRPi {Γ : Ctx} {A : Term} (PiA : PiRedTy Γ A) (PiAad : PiRedTyAdequate (LR rec) PiA) :
    LR rec Γ A
      (fun B   => [ Γ ⊨Π A ≃ B     | PiA ])
      (fun t   => [ Γ ⊨Π t     : A | PiA ])
      (fun t u => [ Γ ⊨Π t ≃ u : A | PiA ])
  | LRNat {Γ A} (NA : [Γ ⊨ℕ A]) :
    LR rec Γ A (NatRedTyEq NA) (NatRedTm NA) (NatRedTmEq NA)
  | LREmpty {Γ A} (NA : [Γ ⊨⊥ A]) :
    LR rec Γ A (EmptyRedTyEq NA) (EmptyRedTm NA) (EmptyRedTmEq NA)
  | LRSig {Γ : Ctx} {A : Term} (SigA : SigRedTy Γ A) (SigAad : SigRedTyAdequate (LR rec) SigA) :
    LR rec Γ A (SigRedTyEq SigA) (SigRedTm SigA) (SigRedTmEq SigA)
  | LRId {Γ A} (IA : IdRedTyPack Γ A) (IAad : IdRedTyAdequate (LR rec) IA) :
    LR rec Γ A
      (IdRedTyEq IA)
      (IdRedTm IA)
      (IdRedTmEq IA)
