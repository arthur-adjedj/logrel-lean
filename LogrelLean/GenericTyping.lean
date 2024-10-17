import LogrelLean.NormalForms

class WfCtx where
 wf_Ctx : Ctx -> Type
class WfType where
 wf_type : Ctx -> Term -> Type
class Typing where
 typing : Ctx -> Term -> Term -> Type
class Inferring where
 inferring : Ctx -> Term -> Term -> Type
class InferringRed where
 infer_red : Ctx -> Term -> Term -> Type
class Checking where
 check : Ctx -> Term -> Term -> Type
class ConvType where
 conv_type : Ctx -> Term -> Term -> Type
class ConvTypeRed where
 conv_type_red : Ctx -> Term -> Term -> Type
class ConvTerm where
 conv_Term : Ctx -> Term -> Term -> Term -> Type
class ConvTermRed where
 conv_Term_red : Ctx -> Term -> Term -> Term -> Type
class ConvNeu where
 conv_neu : Ctx -> Term -> Term -> Term -> Type
class ConvNeuRed where
 conv_neu_red : Ctx -> Term -> Term -> Term -> Type
class ConvNeuConv where
 conv_neu_conv : Ctx -> Term -> Term -> Term -> Type

notation "[" "⊢" Γ "]" => WfCtx.wf_Ctx Γ
notation "[" Γ "⊢"  A "]" => WfType.wf_type Γ A
notation "[" Γ "⊢" t ":" A "]" => Typing.typing Γ A t
notation "[" Γ "⊢" x "▸" A "]" => Inferring.inferring Γ A x
notation "[" Γ "⊢" x "▸ₕ" A "]" => InferringRed.infer_red Γ A x
notation "[" Γ "⊢" x "◃" A "]" => Checking.check Γ A x
notation "[" Γ "⊢" A "≃" B "]" => ConvType.conv_type Γ A B
notation "[" Γ "⊢" A "≃ₕ" B "]" => ConvTypeRed.conv_type_red Γ A B
notation "[" Γ "⊢" x "≃" y ":" A "]" => ConvTerm.conv_Term Γ A x y
notation "[" Γ "⊢" x "≃ₕ" y ":" A "]" => ConvTermRed.conv_Term_red Γ A x y
/-Neutral n and n' are convertible in Γ, inferring the type A-/
notation "[" Γ "⊢" x "~" y "▸" A "]" => ConvNeu.conv_neu Γ A x y
/-Whnfs t and t' are convertible in Γ-/
notation "[" Γ "⊢" x "~ₕ" y "▸" A "]" => ConvNeuRed.conv_neu_red Γ A x y
/-Neutral n and n' are convertible in Γ at type A-/
notation "[" Γ "⊢" x "~" y ":" A "]" => ConvNeuConv.conv_neu_conv Γ A x y


class RedType where
 red : Ctx -> Term -> Term -> Type
class OneStepRedTerm where
 red : Ctx -> Term -> Term -> Term -> Type
class RedTerm where
 red : Ctx -> Term -> Term -> Term -> Type

notation "[" Γ "⊢" t  "⤳" u ":" A  "]" => OneStepRedTerm.red Γ A t u
notation "[" Γ "⊢" A  "⤳*" B "]" => RedType.red Γ A B
notation "[" Γ "⊢" t  "⤳*" u ":" A  "]" => RedTerm.red Γ A t u

variable [WfCtx] [WfType] [Typing] [ConvType] [ConvTerm] [ConvNeuConv] [RedType] [RedTerm]

structure TypeRedWhnf (Γ : Ctx) (A B : Term) : Type where
  red : [ Γ ⊢ A ⤳* B ]
  whnf : Whnf B

structure TermRedWhnf (Γ : Ctx) (A t u : Term) : Type where
  red : [ Γ ⊢ t ⤳* u : A ]
  whnf : Whnf u

structure TypeConvWF (Γ : Ctx) (A B : Term) : Type where
  wf_l : [Γ ⊢ A]
  wf_r : [Γ ⊢ B]
  conv : [Γ ⊢ A ≃ B]

structure TermConvWF (Γ : Ctx) (A t u : Term) : Type where
  wf_l : [Γ ⊢ t : A]
  wf_r : [Γ ⊢ u : A]
  conv : [Γ ⊢ t ≃ u : A]

structure TypeRedWF (Γ : Ctx) (A B : Term) : Type where
  wf_r   : [Γ ⊢ B]
  red : [Γ ⊢ A ⤳* B]

structure TermRedWF (Γ : Ctx) (A t u : Term) : Type where
  wf_r : [Γ ⊢ u : A]
  red : [Γ ⊢ t ⤳* u : A]
notation "[" Γ "⊢" A "↘" B "]" => TypeRedWhnf Γ A B
notation "[" Γ "⊢" t "↘" u ":" A "]" => TermRedWhnf Γ A t u
notation "[" Γ "⊢" A ":≃:" B "]" => TypeConvWF Γ A B
notation "[" Γ "⊢" t ":≃:" u ":" A "]" => TermConvWF Γ A t u
notation "[" Γ "⊢" A ":⤳*:" B "]" => TypeRedWF Γ A B
notation "[" Γ "⊢" t ":⤳*:" u ":" A "]" => TermRedWF Γ A t u
--notation "[" Γ "⊢ₛ" σ ":" A "]" => WellSubst Γ A σ
--notation "[" Γ "⊢ₛ" σ "≃" τ ":" A "]" => ConvSubst Γ A σ τ
--notation "[" "⊢" Γ "≃" Δ "]" => ConvCtx Γ Δ
