import Algebraic.Signature
import Algebraic.Interpretation
import Algebraic.Homomorphism

namespace Algebraic

/-- A wire is either an original input or the output of an earlier gate. -/
abbrev Wire n g := Fin (n + g)

/-- One gate together with the wires supplying its arguments. -/
structure Line (σ : Signature) (n g : Nat) where
  op : σ.Op
  wires : Fin (σ.Arity op) → Wire n g

/-- A topologically ordered straight-line program of `g` gates. -/
inductive Program (σ : Signature) (n : Nat) : Nat → Type v where
  | empty : Program σ n 0
  | gate : Program σ n g → Line σ n g → Program σ n (g + 1)

/-- Evaluate a line from the values of the inputs and preceding gates. -/
def Line.eval
  (line : Line σ n g)
  (i : Interpretation σ U)
  (inputs : Fin n → U)
  (gates : Fin g → U) : U :=
  i line.op (Fin.addCases inputs gates ∘ line.wires)

/-- The depth of a line, given the depth of every wire it may read. -/
def Line.depth
  (line : Line σ n g)
  (wireDepths : Wire n g → Nat) : Nat :=
  Nat.succ <| Fin.foldl (σ.Arity line.op)
    (fun depth k => max depth (wireDepths (line.wires k))) 0

/-- Evaluating a line commutes with a homomorphism. -/
theorem Line.map_eval
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (line : Line σ n g)
  (h : Homomorphism i₁ i₂)
  (inputs : Fin n → U₁)
  (gates : Fin g → U₁) :
  h.map (line.eval i₁ inputs gates) =
    line.eval i₂ (h.map ∘ inputs) (h.map ∘ gates) := by
  rw [Line.eval, Line.eval, h.homomorphic]
  congr 1
  funext k
  simp only [Function.comp_apply]
  exact Fin.addCases (fun _ => by simp) (fun _ => by simp) (line.wires k)

/-- Evaluate every gate in a program, in program order. -/
def Program.eval
  (p : Program σ n g)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin g → U :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.eval i x
      Fin.lastCases (line.eval i x prior) prior

/-- The depth of every gate in a program. Inputs have implicit depth zero. -/
def Program.depths (p : Program σ n g) : Fin g → Nat :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.depths
      let wireDepths := Fin.addCases (fun _ => 0) prior
      Fin.lastCases (line.depth wireDepths) prior

/-- The depth of every input or gate wire in a program. -/
def Program.wireDepths (p : Program σ n g) : Wire n g → Nat :=
  Fin.addCases (fun _ => 0) p.depths

/-- The maximum depth of any gate in a program. -/
def Program.depth (p : Program σ n g) : Nat :=
  Fin.foldl g (fun depth k => max depth (p.depths k)) 0

/-- Evaluating a program commutes with a homomorphism. -/
theorem Program.map_eval
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (p : Program σ n g)
  (h : Homomorphism i₁ i₂)
  (x : Fin n → U₁) :
  h.map ∘ p.eval i₁ x = p.eval i₂ (h.map ∘ x) := by
  induction p with
  | empty =>
      funext k
      exact Fin.elim0 k
  | gate p line ih =>
      funext k
      refine Fin.lastCases ?_ ?_ k
      · simpa only [Program.eval, Function.comp_apply, Fin.lastCases_last, ih] using
          line.map_eval h x (p.eval i₁ x)
      · intro j
        simpa only [Program.eval, Function.comp_apply, Fin.lastCases_castSucc] using
          congrFun ih j

/-- The input values followed by all gate values, in program order. -/
def Program.trace
  (p : Program σ n g)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin (n + g) → U :=
  Fin.addCases x (p.eval i x)

end Algebraic
