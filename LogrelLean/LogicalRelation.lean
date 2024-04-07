import LogrelLean.Ast
import LogrelLean.UntypedReduction


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

notation A "<<" B => TypeLevel.Lt A B

structure NeRedTy (Γ : Ctx) (A : Term) : Type where
  ty : Term
  --red : [ Γ ⊢ \]
