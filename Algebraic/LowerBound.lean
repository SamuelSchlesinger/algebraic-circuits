import Algebraic.LowerBound.AC0.NormalForm
import Algebraic.LowerBound.AC0.LiteralGate
import Algebraic.LowerBound.AC0.BottomGate
import Algebraic.LowerBound.AC0.DecisionTree
import Algebraic.LowerBound.AC0.DecisionTreeTrace
import Algebraic.LowerBound.AC0.Duality
import Algebraic.LowerBound.AC0.TreeNormalForm
import Algebraic.LowerBound.AC0.Layer
import Algebraic.LowerBound.AC0.LayerFormula
import Algebraic.LowerBound.AC0.CanonicalDecisionTree
import Algebraic.LowerBound.AC0.RandomRestriction
import Algebraic.LowerBound.AC0.RestrictionAveraging
import Algebraic.LowerBound.AC0.Switching.Encoding
import Algebraic.LowerBound.AC0.Switching.CombinedAdvice
import Algebraic.LowerBound.AC0.Switching.CanonicalEncoding
import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalEncoding
import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalTrace
import Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking
import Algebraic.LowerBound.AC0.Switching.Canonical
import Algebraic.LowerBound.AC0.Switching.CombinedCanonical
import Algebraic.LowerBound.AC0.Switching
import Algebraic.LowerBound.AC0.Switching.Family
import Algebraic.LowerBound.AC0.BottomFamily
import Algebraic.LowerBound.AC0.LayerSwitching
import Algebraic.LowerBound.AC0.LayerSwitchingBounds
import Algebraic.LowerBound.AC0.LayerExistence
import Algebraic.LowerBound.AC0.LayerExistenceBounds
import Algebraic.LowerBound.AC0.LayerIteration
import Algebraic.LowerBound.AC0.LayerIterationBounds
import Algebraic.LowerBound.AC0.LayerSchedule
import Algebraic.LowerBound.AC0.Parity
import Algebraic.LowerBound.AC0.ParityParameters
import Algebraic.LowerBound.AC0.ParitySurvivors
import Algebraic.LowerBound.AC0.ParityNormalForm
import Algebraic.LowerBound.AC0.ParityCircuit
import Algebraic.LowerBound.AC0.ParityTopGate
import Algebraic.LowerBound.AC0.ParityDepthReduction
import Algebraic.LowerBound.AC0.ParityLowerBound
import Algebraic.LowerBound.FanIn
import Algebraic.LowerBound.Counting
import Algebraic.LowerBound.GateElimination
import Algebraic.LowerBound.Approximation
import Algebraic.LowerBound.Fusion
import Algebraic.LowerBound.Monotone.Clique.Exponential

/-!
# Circuit lower bounds

This umbrella module collects the library's circuit lower-bound methods.
-/
