import Std

/-!
# Standard-library import-only resource baseline

This diagnostic intentionally declares no definition or theorem. Comparing
its bounded compilation with `LocalCheckCoreImports` measures the effect of
loading the cached project core separately from elaborating a new declaration.
It is not a mathematical regression or evidence that a larger module fits.
-/
