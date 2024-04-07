import LogrelLean.Ast

abbrev Ctx := List Term

notation "ε" => (List.nil : Ctx)

notation:60 Γ:60 ",," d:61 => d::Γ
notation:60 Γ:60 ",,," Δ:61 => Δ ++ Γ

inductive InCtx : Ctx → Nat → Term → Type :=
  | here : InCtx (Γ,,d) 0 d⟨↑⟩
  | there : InCtx Γ n d → InCtx (Γ,,d') n.succ d⟨↑⟩

theorem InCtx.inj : InCtx Γ n decl → InCtx Γ n decl' → decl = decl'
  | here, here => rfl
  | there t₁, there t₂ => congrArg _ (InCtx.inj t₁ t₂)
