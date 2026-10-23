"""Guard the consolidated guides without treating historical prose as policy.

The archive retains exact original guide bytes, not just selected quotations.
Existing proof/inventory hashes still check their original content through
``archived_text``. Link checks concern live guides only: obsolete paths inside
verbatim historical snapshots are evidence, not broken current navigation.
"""

import hashlib
from pathlib import Path
import re
import unittest


def archived_text(lean_root, original_path):
    archive = (lean_root / "HISTORY.md").read_text()
    beginning = "<!-- BEGIN ARCHIVE " + original_path + " -->\n````markdown\n"
    ending = "````\n<!-- END ARCHIVE " + original_path + " -->"
    if archive.count(beginning) != 1 or archive.count(ending) != 1:
        raise AssertionError("missing or ambiguous archived guide: " + original_path)
    return archive.split(beginning, 1)[1].split(ending, 1)[0]


def anchors(text):
    result = set(re.findall(r'<a id="([^"]+)"', text))
    # These guides use ordinary GitHub heading anchors. Repeated titles get
    # numeric suffixes; explicit stable topic anchors remain preferable.
    counts = {}
    for heading in re.findall(r"(?m)^#{1,6} (.+)$", text):
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        number = counts.get(slug, 0)
        counts[slug] = number + 1
        result.add(slug + ("-" + str(number) if number else ""))
    return result


class DocumentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = Path(__file__).resolve().parents[1]
        cls.root = cls.lean.parent

    def test_original_guides_are_preserved_verbatim(self):
        originals = {
            "README.md": "4b9500efeb917c43a687328ff66bbcfdc336d9937def34590ec990ff1a2f4983",
            "lean/REFACTORING.md": "4165c2df0c8cf237bd0bac8cbf32a6d9653e1842acaa232db7d2203bc29a75b3",
            "lean/LOCAL_CHECKS.md": "61bbcb0a39d768b3463fb64ed3d210d9324c75a2987da352eeb21509faaa5547",
            "lean/THEOREM_COVERAGE.md": "68bd7023926059be1d130a7dba1e8575a1ffc5979de71fd42fede688786f544d",
            "lean/ENTROPY.md": "67d02c57b0675180ff614f18a9de058822968ed4f4773ece6d42b4ec528d68e3",
            "lean/docs/structure.md": "3c99d0a75f794f618d3aa4de7989baeed8b4037c547299d87a8b604e09327c34",
            "lean/docs/history/refactoring-pass1.md": "6417157544ba085b8d668ecbd9aff4f7181102638ab153cf92b678a0919ced77",
            "lean/docs/history/completeness-development.md": "0583aafd792a5fbf68de03d356fbd0f60ea507665a0228cbd2792e341baeecdb",
        }
        for path, expected in originals.items():
            with self.subTest(path=path):
                body = archived_text(self.lean, path)
                self.assertEqual(hashlib.sha256(body.encode()).hexdigest(), expected)
                if path != "README.md":
                    self.assertFalse((self.root / path).exists(), "do not recreate superseded guides")

    def test_live_guide_links_resolve(self):
        for name in ("README.md", "lean/AGENTS.md", "lean/REFERENCE.md"):
            source = self.root / name
            for target in re.findall(r"\]\(([^)]+)\)", source.read_text()):
                if re.match(r"(?:https?://|mailto:)", target):
                    continue
                with self.subTest(source=name, target=target):
                    location, _, anchor = target.partition("#")
                    destination = source.parent / location if location else source
                    self.assertTrue(destination.exists(), "missing current navigation target")
                    if anchor and destination.suffix == ".md":
                        self.assertIn(anchor, anchors(destination.read_text()))

    def test_current_operating_policy_is_separate_from_history(self):
        policy = (self.lean / "AGENTS.md").read_text()
        for text in ("propext", "Quot.sound", "4608", "5120", "30 seconds",
                     "lake build Thesis.AxiomAudit", "lake build Thesis.DistroAxiomAudit",
                     "lake build Thesis.ConstructiveAlgebraAudit", "frozen read-only acceptance"):
            self.assertIn(text, policy)
        self.assertIn("History is evidence, not current instructions", policy)
        self.assertIn("Unresolved research boundaries", (self.lean / "REFERENCE.md").read_text())


if __name__ == "__main__":
    unittest.main()
