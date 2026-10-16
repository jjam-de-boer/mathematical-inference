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


if __name__ == "__main__":
    unittest.main()
