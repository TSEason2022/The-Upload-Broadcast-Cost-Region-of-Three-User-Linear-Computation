import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-- Toolchain smoke test only; this is not a claim from the paper. -/
theorem toolchain_smoke (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

#print axioms toolchain_smoke
