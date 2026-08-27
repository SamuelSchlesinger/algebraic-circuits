import Algebraic.Translation

/-!
# Polarity propagation

The four-point polarity domain records independence, positive dependence,
negative dependence, or mixed dependence. A local polarity for each operation
argument induces a compositional analysis of every circuit. As with degree, a
concrete monotonicity theorem only needs to establish soundness of the selected
local policy.
-/

namespace Algebraic

/-- Abstract dependence polarity. -/
inductive Polarity
  | none
  | positive
  | negative
  | mixed
  deriving DecidableEq, Repr

namespace Polarity

/-- Join information coming from two dependency paths. -/
def join : Polarity → Polarity → Polarity
  | .none, right => right
  | left, .none => left
  | .mixed, _ | _, .mixed => .mixed
  | .positive, .positive => .positive
  | .negative, .negative => .negative
  | .positive, .negative | .negative, .positive => .mixed

/-- Compose the polarity of an operation argument with the polarity carried by
the argument expression. -/
def comp : Polarity → Polarity → Polarity
  | .none, _ | _, .none => .none
  | .positive, inner => inner
  | .negative, .positive => .negative
  | .negative, .negative => .positive
  | .negative, .mixed => .mixed
  | .mixed, _ => .mixed

/-- One-hot positive dependency profile of an original input. -/
def inputProfile (input : Fin n) : Fin n → Polarity :=
  fun coordinate => if input = coordinate then .positive else .none

end Polarity

/-- Local polarity of every argument of every operation. -/
abbrev PolarityPolicy (σ : Signature) :=
  (op : σ.Op) → Fin (σ.Arity op) → Polarity

/-- Polarity interpretation induced by a local argument policy. -/
def Signature.polarityInterpretation
    (σ : Signature)
    (policy : PolarityPolicy σ)
    (n : Nat) : Interpretation σ (Fin n → Polarity) :=
  fun op input coordinate =>
    Fin.foldl (σ.Arity op)
      (fun result argument =>
        result.join ((policy op argument).comp (input argument coordinate)))
      .none

/-- Per-output, per-input polarity profile of a circuit. -/
def Circuit.polarityProfile
    (circuit : Circuit σ n g m)
    (policy : PolarityPolicy σ) : Fin m → Fin n → Polarity :=
  circuit.eval (σ.polarityInterpretation policy n) Polarity.inputProfile

/-- Translation preserves the exact abstract polarity propagation induced by
its target operation gadgets. -/
theorem Translation.compile_polarityProfile
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m)
    (targetPolicy : PolarityPolicy τ) :
    (translation.compile circuit).polarityProfile targetPolicy =
      circuit.eval
        (translation.pull (τ.polarityInterpretation targetPolicy n))
        Polarity.inputProfile := by
  exact translation.compile_eval circuit
    (τ.polarityInterpretation targetPolicy n) Polarity.inputProfile

end Algebraic
