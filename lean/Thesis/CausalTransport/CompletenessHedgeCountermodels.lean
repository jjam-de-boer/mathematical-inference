import Thesis.CausalTransport.CompletenessHedgeParity
import Thesis.CausalTransport.Hedge.Countermodels

/-!
# Compatibility import for the original hedge-countermodel layer

`Hedge.Countermodels` owns the unchanged observational equalities and qualified
mix constructions. This path also retains the preceding historical imports,
so existing clients keep the same public declarations. Current mathematics
should import the focused owner rather than inheriting historical engine
proofs for the finite countermodel lemmas alone.
-/
