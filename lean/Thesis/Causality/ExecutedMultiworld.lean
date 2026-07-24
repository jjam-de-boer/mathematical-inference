import Thesis.Causality.ExecutedMultiworld.Creation
import Thesis.Causality.ExecutedMultiworld.Linking
import Thesis.Causality.ExecutedMultiworld.Configuration
import Thesis.Causality.ExecutedMultiworld.Endpoint
import Thesis.Causality.ExecutedMultiworld.FromFactual
import Thesis.Causality.ExecutedMultiworld.EmptyConstruction
import Thesis.Causality.ExecutedMultiworld.FromEmpty
import Thesis.Causality.ExecutedMultiworld.Agreement

/-!
Stable facade for the two executable occurrence-indexed multiworld routes.

`Creation` and `Linking` create typed copies of roots and observed nodes.
`FromFactual` starts with a fresh factual mode; `EmptyConstruction` and
`FromEmpty` instead create every required root and node from the literal empty
mode.  Both routes end in actual epistemic records, rather than merely a
reference multiworld model.  `Agreement` compares their endpoints after the
necessary dependent-coordinate transport.
-/
