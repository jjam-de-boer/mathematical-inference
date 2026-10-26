"""Keep standalone examples inside the full proof-policy gate's imports.

Importing a library theorem does not elaborate a separate regression file
that exercises it. This inexpensive source-graph check protects against that
coverage gap recurring. It never invokes Lean, and is not itself a proof or
axiom check: the complete build and Thesis.AxiomAudit remain authoritative.
"""

from pathlib import Path
import unittest


def initial_project_imports(source):
    """Read ordinary initial imports, never import-like text in body comments.

    The repository uses one plain header block. An unsupported leading header
    is conservatively treated as having no imports, not searched through for
    text that might falsely make an otherwise orphaned example seem covered.
    """
    dependencies = []
    for line in source.splitlines():
        header = line.strip()
        if not header:
            continue
        if not header.startswith("import "):
            break
        for module in header.removeprefix("import ").split("--", 1)[0].split():
            if module == "Thesis" or module.startswith("Thesis."):
                dependencies.append(module)
    return dependencies


def reachable(graph, root):
    seen, pending = set(), [root]
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph.get(module, []))
    return seen


def is_policy_module(module):
    return module == "Thesis.AxiomAudit" or module.startswith("Thesis.AxiomPolicy")


def distros_module(module):
    return (module == "Thesis.Probability.Distros" or
            module.startswith("Thesis.Probability.Distros."))


def prefix_owner(module):
    """Match Thesis.AxiomPolicy.Elaborator.owner? on mathematical modules."""
    if is_policy_module(module):
        return None
    if distros_module(module):
        return "distros"
    if module == "Thesis.Probability" or module.startswith("Thesis.Probability."):
        return "probability"
    if module == "Thesis.Causality" or module.startswith("Thesis.Causality."):
        return "causality"
    if module == "Thesis.CausalTransport" or module.startswith("Thesis.CausalTransport."):
        return "causalTransport"
    if module == "Thesis" or module == "Thesis.Examples" or module.startswith("Thesis.Examples."):
        return "examples"
    return None


class ExampleCoverageTests(unittest.TestCase):
    def test_imports_ignore_body_comments_and_keep_root_facade(self):
        self.assertEqual(initial_project_imports(
            "import Thesis\nimport Thesis.Examples.Left -- fixture\n"
            "namespace Thesis\n/-\nimport Thesis.Examples.Orphan\n-/\n"),
            ["Thesis", "Thesis.Examples.Left"])

    def test_reachability_follows_transitive_imports_without_looping(self):
        self.assertEqual(reachable({"Audit": ["Facade"], "Facade": ["Example"],
                                    "Example": ["Facade"]}, "Audit"),
                         {"Audit", "Facade", "Example"})

    def test_every_example_is_reached_by_full_axiom_audit(self):
        root = Path(__file__).resolve().parents[1]
        sources = [root / "Thesis.lean", *(root / "Thesis").rglob("*.lean")]
        graph = {".".join(source.relative_to(root).with_suffix("").parts):
                 initial_project_imports(source.read_text()) for source in sources}
        covered = reachable(graph, "Thesis.AxiomAudit")
        missing = sorted(module for module in graph
                         if module.startswith("Thesis.Examples.") and module not in covered)
        self.assertFalse(missing, "Examples outside the full axiom-audit import closure: "
                         + ", ".join(missing))
        self.assertIn("Thesis.AxiomPolicy.Coverage", covered)
        self.assertIn("Thesis.AxiomPolicy.Distros", covered)
        self.assertIn("Thesis.AxiomPolicy.IdentificationNames", covered)

    def test_every_mathematical_module_has_exactly_one_axiom_prefix(self):
        root = Path(__file__).resolve().parents[1]
        sources = [root / "Thesis.lean", *(root / "Thesis").rglob("*.lean")]
        unowned = []
        for source in sources:
            module = ".".join(source.relative_to(root).with_suffix("").parts)
            if is_policy_module(module):
                self.assertIsNone(prefix_owner(module), module)
                continue
            owner = prefix_owner(module)
            if owner is None:
                unowned.append(module)
        self.assertFalse(unowned, "Thesis modules outside every axiom-policy prefix: "
                         + ", ".join(unowned))
        self.assertEqual(prefix_owner("Thesis.Probability.Distros.Entropy"), "distros")
        self.assertEqual(prefix_owner("Thesis.Probability.Core"), "probability")
        self.assertEqual(prefix_owner("Thesis.Causality.Graph"), "causality")
        self.assertEqual(prefix_owner("Thesis.CausalTransport.Soundness"), "causalTransport")
        self.assertEqual(prefix_owner("Thesis.Examples.IdentificationRegression"), "examples")
        self.assertEqual(prefix_owner("Thesis"), "examples")


if __name__ == "__main__":
    unittest.main()
