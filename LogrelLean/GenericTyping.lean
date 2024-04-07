import LogrelLean.NormalForms

class WfContext where
 wf_context : context -> Type
class WfType where
 wf_type : context -> term -> Type
class Typing where
 typing : context -> term -> term -> Type
class Inferring where
 inferring : context -> term -> term -> Type
class InferringRed where
 infer_red : context -> term -> term -> Type
class Checking where
 check : context -> term -> term -> Type
class ConvType where
 conv_type : context -> term -> term -> Type
class ConvTypeRed where
 conv_type_red : context -> term -> term -> Type
class ConvTerm where
 conv_term : context -> term -> term -> term -> Type
class ConvTermRed where
 conv_term_red : context -> term -> term -> term -> Type
class ConvNeu where
 conv_neu : context -> term -> term -> term -> Type
class ConvNeuRed where
 conv_neu_red : context -> term -> term -> term -> Type
class ConvNeuConv where
 conv_neu_conv : context -> term -> term -> term -> Type

notation "[" "⊢" Γ "]" => WfContext.wf_context Γ
notation "[" Γ "⊢"  A "]" => WfType.wf_type Γ A
notation "[" Γ "⊢" t ":" A "]" => Typing.typing Γ A t
notation "[" Γ "⊢" x "▸" A "]" => Inferring.inferring Γ A x
notation "[" Γ "⊢" x "▸ₕ" A "]" => InferringRed.infer_red Γ A x
notation "[" Γ "⊢" x "◃" A "]" => Checking.check Γ A x
notation "[" Γ "⊢" A "≃" B "]" => ConvType.conv_type Γ A B
notation "[" Γ "⊢" A "≃ₕ" B "]" => ConvTypeRed.conv_type_red Γ A B
notation "[" Γ "⊢" x "≃" y ":" A "]" => ConvTerm.conv_term Γ A x y
notation "[" Γ "⊢" x "≃ₕ" y ":" A "]" => ConvTermRed.conv_term_red Γ A x y
/-Neutral n and n' are convertible in Γ, inferring the type A-/
notation "[" Γ "⊢" x "~" y "▸" A "]" => ConvNeu.conv_neu Γ A x y
/-Whnfs t and t' are convertible in Γ-/
notation "[" Γ "⊢" x "~ₕ" y "▸" A "]" => ConvNeuRed.conv_neu_red Γ A x y
/-Neutral n and n' are convertible in Γ at type A-/
notation "[" Γ "⊢" x "~" y ":" A "]" => ConvNeuConv.conv_neu_conv Γ A x y


class RedType where
 red : context -> term -> term -> Type
class OneStepRedTerm where
 red : context -> term -> term -> term -> Type
class RedTerm where
 red : context -> term -> term -> term -> Type

notation "[" Γ "⊢" t  "⤳" u ":" A  "]" => OneStepRedTerm.red Γ A t u
notation "[" Γ "⊢" A  "⤳*" B "]" => RedType.red Γ A B
notation "[" Γ "⊢" t  "⤳*" u ":" A  "]" => RedTerm.red Γ A t u

variable [WfContext] [WfType] [Typing] [ConvType] [ConvTerm] [ConvNeuConv] [RedType] [RedTerm]

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
