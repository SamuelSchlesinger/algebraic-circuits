import Algebraic.LowerBound.Fusion.Framework
import Algebraic.LowerBound.Fusion.Arithmetic
import Algebraic.LowerBound.Fusion.Arithmetic.Degree
import Algebraic.LowerBound.Fusion.Semifilter
import Algebraic.LowerBound.Fusion.Cyclic
import Algebraic.LowerBound.Fusion.Cyclic.Closure
import Algebraic.LowerBound.Fusion.Cyclic.JoinMeet
import Algebraic.LowerBound.Fusion.Cyclic.Compiler
import Algebraic.LowerBound.Fusion.Boolean
import Algebraic.LowerBound.Fusion.Pullback
import Algebraic.LowerBound.Fusion.Conondeterministic
import Algebraic.LowerBound.Fusion.Neq
import Algebraic.LowerBound.Fusion.Conondeterministic.Neq
import Algebraic.LowerBound.Fusion.Cyclic.Neq

/-!
# Fusion lower bounds

This umbrella exports the algebra-generic fusion engine, its semi-filter
set-cover specialization, and the pointwise Boolean interfaces.

The semi-filter layer formalizes the acyclic lower-bound direction of the
modern cover-complexity presentation.  The converse via cyclic circuits is a
different computational model and is intentionally not folded into
`Program`.

References:

* A. Wigderson, *The Fusion Method for Lower Bounds in Circuit Complexity*
  (1993).
* B. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and
  Two-Dimensional Cover Problems* (2025), https://arxiv.org/abs/2503.14117.
* J. Pich, *Localizability of the Approximation Method* (2022),
  https://arxiv.org/abs/2212.09285.
-/
