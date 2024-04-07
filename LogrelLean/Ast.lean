import Std.CodeAction
import Aesop

attribute [symm] Eq.symm

@[simp]
def scons (x : X) (ξ : Nat → X) : Nat → X
  | 0 => x
  | n+1 => ξ n

notation s ".:" σ => scons s σ

inductive Sort' : Type :=
  | set : Sort'

def Sort'.product (_s _s' : Sort') := Sort'.set

inductive Term : Type :=
  | tRel       : Nat → Term
  | tSort      : Sort' → Term
  | tProd      : Term → Term → Term
  | tLambda    : Term → Term → Term
  | tApp       : Term → Term → Term
  | tNat       : Term
  | tZero      : Term
  | tSucc      : Term → Term
  | tNatElim   : Term → Term → Term → Term → Term
  | tEmpty     : Term
  | tEmptyElim : Term → Term → Term
  | tSig       : Term → Term → Term
  | tPair      : Term → Term → Term → Term → Term
  | tFst       : Term → Term
  | tSnd       : Term → Term
  | tId        : Term → Term → Term → Term
  | tRefl      : Term → Term → Term
  | tIdElim    : Term → Term → Term → Term → Term → Term → Term
open Term

namespace Term


syntax:max term noWs ".." : term
macro_rules
  | `($s..)=> `($s .: tRel)

notation "𝒰" => Term.tSort Sort'.set

abbrev shift := Nat.succ
notation "↑" => shift

def up_ren (σ : Nat → Nat) : Nat → Nat :=
  0 .: (↑ ∘ σ)

def ren (f : Nat → Nat) : Term → Term := fun
  | tRel n => tRel (f n)
  | tSort s => tSort s
  | tProd a b => tProd (a.ren f) (b.ren (up_ren f))
  | tLambda a b => tLambda (a.ren f) (b.ren (up_ren f))
  | tApp a b => tApp (a.ren f) (b.ren f)
  | tNat => tNat
  | tZero => tZero
  | tSucc n => tSucc (n.ren f)
  | tNatElim motive pzero psucc n =>
    tNatElim (motive.ren (up_ren f)) (pzero.ren f) (psucc.ren f) (n.ren f)
  | tEmpty => tEmpty
  | tEmptyElim motive ff => tEmptyElim (motive.ren (up_ren f)) (ff.ren f)
  | tSig a b => tSig (a.ren f) (b.ren (up_ren f))
  | tPair a b x y => tPair (a.ren f) (b.ren (up_ren f)) (x.ren f) (y.ren f)
  | tFst p => tFst (p.ren f)
  | tSnd p => tSnd (p.ren f)
  | tId a x y => tId (a.ren f) (x.ren f) (y.ren f)
  | tRefl a b => tRefl (a.ren f) (b.ren f)
  | tIdElim A x motive p y h =>
    tIdElim (A.ren f) (x.ren f) (motive.ren (up_ren (up_ren f)))
      (p.ren f) (y.ren f) (h.ren f)

@[simp]
theorem id_up_ren : up_ren id = id:= by
  funext t
  induction t
  · rfl
  · simp [up_ren,ren]

@[simp]
theorem ren_id_id {t : Term}: t.ren id = t := by
  induction t <;>
  rw [ren] <;>
  aesop

syntax:max term noWs "⟨" term "⟩" : term
macro_rules
  | `($t⟨$f⟩)=> `(Term.ren $f $t)

def up_term (σ : Nat → Term) : Nat → Term :=
   tRel 0 .: Term.ren shift ∘ σ

def subst (f : Nat → Term) : Term → Term := fun
  | tRel n => f n
  | tSort s => tSort s
  | tProd a b => tProd (a.subst f) (b.subst (up_term f))
  | tLambda a b => tLambda (a.subst f) (b.subst (up_term f))
  | tApp a b => tApp (a.subst f) (b.subst f)
  | tNat => tNat
  | tZero => tZero
  | tSucc n => tSucc (n.subst f)
  | tNatElim motive pzero psucc n =>
    tNatElim (motive.subst (up_term f)) (pzero.subst f) (psucc.subst f) (n.subst f)
  | tEmpty => tEmpty
  | tEmptyElim motive ff => tEmptyElim (motive.subst f) (ff.subst f)
  | tSig a b => tSig (a.subst f) (b.subst (up_term f))
  | tPair a b x y => tPair (a.subst f) (b.subst (up_term f)) (x.subst f) (y.subst f)
  | tFst p => tFst (p.subst f)
  | tSnd p => tSnd (p.subst f)
  | tId a x y => tId (a.subst f) (x.subst f) (y.subst f)
  | tRefl a b => tRefl (a.subst f) (b.subst f)
  | tIdElim A x motive p y h =>
    tIdElim (A.subst f) (x.subst f) (motive.subst (up_term (up_term f)))
      (p.subst f) (y.subst f) (h.subst f)


instance : GetElem Term (Nat → Term) Term (fun _ _ => True) where
  getElem t f _ := t.subst f

syntax:max term noWs "[" withoutPosition(term) "]⇑" : term
macro_rules
  | `($t[$f]⇑) => `($t[$f .: (tRel ∘ ↑)])



theorem id_up_term : up_term tRel = tRel:= by
  funext t
  induction t
  · rfl
  · simp [up_term,ren]

theorem idSubst (t : Term) : t.subst tRel = t := by
  induction t <;>
  rw [subst] <;>
  congr <;>
  simp [id_up_term] <;>
  assumption


@[simp]
theorem up_ren_ren_term_term : (up_ren g ∘ up_ren f) = up_ren (g ∘ f) := by
  funext x
  induction x <;>
  · unfold Function.comp
    rw [up_ren,up_ren,up_ren]
    aesop

theorem compRen (ξ ζ : Nat → Nat) : (Term.ren ξ ∘ Term.ren ζ) = Term.ren (ξ ∘ ζ)
:= by
  funext t
  induction t generalizing ξ ζ <;>
  unfold Function.comp <;>
  rw [ren,ren,ren] <;>
  first
    | rfl
    | aesop

theorem up_ren_subst_term_term:
  (up_term τ) ∘ (up_ren ξ) = up_term (τ ∘ ξ) := by
    funext t
    induction t <;>
    aesop

theorem compSubstRen (ζ : Nat → Nat) (θ : Nat → Term) (t : Term) : (t.subst  θ).ren ζ = t.subst ((ren ζ) ∘ θ) := by
  induction t generalizing ζ θ <;>
  rw [subst,subst] <;>
  first
    | rfl
    | rw [ren]
      congr <;>
      sorry

end Term

namespace Term

abbrev arr A B := tProd A B⟨↑⟩

def elimSuccHypTy P :=
  tProd tNat (arr P P[tSucc (tRel 0)]⇑)
