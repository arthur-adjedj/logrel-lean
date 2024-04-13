import LogrelLean.Context
import LogrelLean.Ast
import Aesop

inductive Wk : Type :=
  | empty
  | step (w : Wk)
  | up (w : Wk)

def Wk.comp : Wk → Wk → Wk
  | empty, ρ' => ρ'
  | step ρ, ρ' => step (comp ρ ρ')
  | up ρ, empty => ρ
  | up ρ, step ρ' => step (comp ρ ρ')
  | up ρ, up ρ' => up (comp ρ ρ')

def Ctx.toWk : Ctx → Wk
  | ε => .empty
  | (Γ : Ctx) ,, _ => .up Γ.toWk

def Wk.toRen : Wk → Nat → Nat
  | empty => id
  | step w => w.toRen ∘ .succ
  | up w => Term.up_ren w.toRen

@[simp]
theorem id_of_toRen_toWk {Γ : Ctx}: Γ.toWk.toRen = id := by
  induction Γ <;>
  simp [Ctx.toWk,Wk.toRen]
  next ih => rw [ih,Term.id_up_ren]

instance : CoeFun Wk (fun _ => Nat → Nat) := ⟨Wk.toRen⟩

theorem Wk.comp_toRen : (comp ρ ρ').toRen = ρ' ∘ ρ := by
  induction ρ,ρ' using Wk.comp.induct <;>
  simp [comp,toRen] <;> sorry

inductive WellWk : Wk → Ctx → Ctx → Type :=
  | empty : WellWk .empty ε ε
  | step : WellWk ρ Γ Δ → WellWk ρ.step (Γ,,A) Δ
  | up : WellWk ρ Γ Δ → WellWk ρ.up (Γ,, A.ren ρ) (Δ,,A)

def well_wk_compose :
  WellWk ρ Δ Δ' → WellWk ρ' Δ' Δ'' → WellWk (ρ.comp ρ') Δ Δ'' := sorry


def Ctx.wellWkId : {Γ : Ctx} → WellWk Γ.toWk Γ Γ
  | ε => .empty
  | (Γ : Ctx),,A => by
    conv =>
      lhs
      rw [show A = A.ren Γ.toWk.toRen by simp]
    exact WellWk.up Ctx.wellWkId

structure WkWellWk (Γ Δ : Ctx) where
  wk : Wk
  wellWk : WellWk wk Γ Δ

instance : CoeOut (WkWellWk Γ Δ) Wk := ⟨WkWellWk.wk⟩
instance : CoeDep (WkWellWk Γ Δ) w (WellWk w.wk Γ Δ) := ⟨WkWellWk.wellWk ..⟩

infixl:60 " ≤ " => WkWellWk
variable {Γ Δ : Ctx}

def WkWellWk.empty: ε ≤ ε := ⟨.empty,.empty⟩

def WkWellWk.step (w: Γ ≤ Δ): Γ,,A ≤ Δ := ⟨.step w,.step w⟩

def WkWellWk.up (w: Γ ≤ Δ): Γ,,A⟨w⟩ ≤ (Δ ,, A) := ⟨.up w,.up w⟩

def WkWellWk.id : Γ ≤ Γ := ⟨_,Ctx.wellWkId⟩

def wk_well_wk_compose {Γ Γ' Γ'' : Ctx} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' := sorry

infixl:60 "∘w" => wk_well_wk_compose

def wk₁ (A) : Γ,, A ≤ Γ := .step (.id ..)
