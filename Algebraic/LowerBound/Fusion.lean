import Algebraic.LowerBound.Fusion.Framework
import Algebraic.LowerBound.Fusion.Substitution
import Algebraic.LowerBound.Fusion.Contextual
import Algebraic.LowerBound.Fusion.Counting
import Algebraic.LowerBound.Fusion.Arithmetic.Atoms
import Algebraic.LowerBound.Fusion.Arithmetic.ExactSupport
import Algebraic.LowerBound.Fusion.Arithmetic.BoundedFailure
import Algebraic.LowerBound.Fusion.Arithmetic.Combined
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction
import Algebraic.LowerBound.Fusion.Arithmetic.Expression
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Local
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Occurrence
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Multiple
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear.Quotient
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Quotient
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Nonlinear
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Mixing
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Squarefree
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Squarefree.Mixing
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairing
import Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairwise
import Algebraic.LowerBound.Fusion.Arithmetic.Support
import Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial
import Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial.Layer
import Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial.Exact
import Algebraic.LowerBound.Fusion.Arithmetic.Progress
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.General
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Expansion
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.MonomialSubstitution
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.WeightedMonomialSubstitution
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Addition
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.PositiveConstants
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Addition
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Exact
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.NNRat
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Unit
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Collision
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Addition
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Polynomial
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.PositiveConstants
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.NaturalConstants
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.NNRat
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.Exact
import Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.Total
import Algebraic.LowerBound.Fusion.Arithmetic
import Algebraic.LowerBound.Fusion.Arithmetic.Degree
import Algebraic.LowerBound.Fusion.SumOfTerms
import Algebraic.LowerBound.Fusion.SumOfTerms.Rank
import Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation
import Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction
import Algebraic.LowerBound.Fusion.SumOfTerms.Coverage
import Algebraic.LowerBound.Fusion.SumOfTerms.Rectangle
import Algebraic.LowerBound.Fusion.Semifilter
import Algebraic.LowerBound.Fusion.Cyclic
import Algebraic.LowerBound.Fusion.Cyclic.Closure
import Algebraic.LowerBound.Fusion.Cyclic.JoinMeet
import Algebraic.LowerBound.Fusion.Cyclic.Compiler
import Algebraic.LowerBound.Fusion.Cyclic.LowerJoinMeet
import Algebraic.LowerBound.Fusion.Cyclic.Complete
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
