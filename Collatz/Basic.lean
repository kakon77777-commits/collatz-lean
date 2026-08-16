import Mathlib.Tactic

/-- Toolchain smoke test: mathlib is importable and `omega` works. -/
example (n : ℕ) (h : 2 * n = 6) : n = 3 := by omega
