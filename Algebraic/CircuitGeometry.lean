import Algebraic.Basis.DeMorgan.Boundary
import Algebraic.Basis.DeMorgan.Homology
import Algebraic.Basis.DeMorgan.Betti
import Algebraic.Basis.DeMorgan.Witness
import Algebraic.Basis.DeMorgan.Locality
import Algebraic.BooleanCube.FaceRealization
import Algebraic.Basis.DeMorgan.StarAsymptotics
import Algebraic.Basis.DeMorgan.StarCycles
import Algebraic.Basis.DeMorgan.StarSubcube

/-!
# Geometry of Boolean circuit complexity

This focused import exposes truth-table sweeps, shortest budgeted paths,
sublevel boundaries and coarea, and the continuous contraction and induced
homology maps for the cubical circuit-complexity filtration. It also exposes
localized lower-bound witnesses and a locality obstruction for cochain certificates.
Constant-star links, their exact input-cube shape at budget `n`, face birth
times, exact graph cycle ranks, structured input-subcube supports, and finite
and asymptotic first-contact bounds are included.
-/
