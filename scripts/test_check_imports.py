"""Regression tests for the public coverage and dependency-boundary CI gate."""

from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from check_imports import check, imports


class ImportChecks(unittest.TestCase):
    def setUp(self):
        self.temporary = TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write("Algebraic", "import Algebraic.Core\nimport Algebraic.Basis.DeMorgan.Complexity")
        self.write("Algebraic.Core", "")
        self.write("Algebraic.Basis.DeMorgan.Complexity", "import Algebraic.Basis.DeMorgan.Completeness")
        self.write("Algebraic.Basis.DeMorgan.Completeness", "")
        self.write("AlgebraicTests", "")

    def write(self, module, source):
        path = self.root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)

    def test_covered_tree(self):
        self.assertEqual(check(self.root), [])

    def test_comments_and_module_headers(self):
        self.assertEqual(imports("""
            /- import Hidden /- nested -/ -/
            module
            -- import AlsoHidden
            public import Algebraic.Core
            import Mathlib.Data.Fin.Basic
            /-! import NotAnImport -/
            namespace Example
        """), ["Algebraic.Core", "Mathlib.Data.Fin.Basic"])

    def test_orphaned_library_and_test(self):
        self.write("Algebraic.NewTheorem", "")
        self.write("AlgebraicTests.NewTest", "")
        errors = check(self.root)
        self.assertIn("Algebraic.lean does not reach Algebraic.NewTheorem", errors)
        self.assertIn("AlgebraicTests.lean does not reach AlgebraicTests.NewTest", errors)

    def test_missing_import(self):
        self.write("Algebraic.Core", "import Algebraic.Missing")
        self.assertIn("Algebraic.Core imports missing local module Algebraic.Missing", check(self.root))

    def test_library_cannot_depend_on_tests(self):
        self.write("Algebraic.Core", "import AlgebraicTests")
        self.assertIn("Library module Algebraic.Core imports test module AlgebraicTests", check(self.root))

    def test_indirect_research_dependency(self):
        self.write("Algebraic.Core", "import Algebraic.Helper")
        self.write("Algebraic.Helper", "import Algebraic.MassProduction")
        self.write("Algebraic.MassProduction", "")
        self.assertIn("Algebraic.Core unexpectedly depends on Algebraic.MassProduction", check(self.root))

    def test_sharp_synthesis_cannot_define_complexity(self):
        self.write("Algebraic.Basis.DeMorgan.Completeness",
                   "import Cslib.Computability.Circuit.Boolean.LupanovConstruction")
        errors = check(self.root)
        self.assertTrue(any("Algebraic.Basis.DeMorgan.Completeness unexpectedly" in e for e in errors))
        self.assertTrue(any("Algebraic.Basis.DeMorgan.Complexity unexpectedly" in e for e in errors))


if __name__ == "__main__":
    unittest.main()
