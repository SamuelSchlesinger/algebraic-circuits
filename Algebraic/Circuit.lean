import Algebraic.Program

namespace Algebraic

/-- A straight-line program followed by a terminal layer of output gates. -/
structure Circuit (σ : Signature) (n g m : Nat) where
  /-- The internal gates of the circuit. -/
  program : Program σ n g
  /-- The terminal gate computing each output. -/
  outputs : Fin m → Line σ n g

/-- Every internal and output gate in a circuit has at most `r` arguments. -/
def Circuit.FanInAtMost (c : Circuit σ n g m) (r : Nat) : Prop :=
  c.program.FanInAtMost r ∧ ∀ k, σ.Arity (c.outputs k).op ≤ r

/-- The total number of internal and output gates in a circuit. -/
def Circuit.size (_ : Circuit σ n g m) : Nat :=
  g + m

/-- The depth of every terminal output gate in a circuit. -/
def Circuit.outputDepths (c : Circuit σ n g m) : Fin m → Nat :=
  fun k => (c.outputs k).depth c.program.wireDepths

/-- The maximum depth of a terminal output gate in a circuit. -/
def Circuit.depth (c : Circuit σ n g m) : Nat :=
  Fin.foldl m (fun depth k => max depth (c.outputDepths k)) 0

/-- Evaluate the terminal output gates of a circuit. -/
def Circuit.eval
  (c : Circuit σ n g m)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin m → U :=
  fun k => (c.outputs k).eval i x (c.program.eval i x)

/-- Evaluating a circuit commutes with a homomorphism. -/
theorem Circuit.map_eval
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (c : Circuit σ n g m)
  (h : Homomorphism i₁ i₂)
  (x : Fin n → U₁) :
  h.map ∘ c.eval i₁ x = c.eval i₂ (h.map ∘ x) := by
  funext k
  simp only [Circuit.eval, Function.comp_apply]
  rw [(c.outputs k).map_eval h x, c.program.map_eval h x]

/-- All internal and output gate values, in that order. -/
def Circuit.computation
  (c : Circuit σ n g m)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin (g + m) → U :=
  Fin.addCases (c.program.eval i x) (c.eval i x)

/-- The input, internal-gate, and output-gate values, in that order. -/
def Circuit.trace
  (c : Circuit σ n g m)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin (n + g + m) → U :=
  Fin.addCases (c.program.trace i x) (c.eval i x)

end Algebraic
