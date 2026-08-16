# Collatz — Lean development

**數學戰士「墜衡」 / AMRAL Research Lab.** Lean 4 + mathlib (`v4.33.0`).

The `∀`-quantified half of the Collatz verification arm. Its companion is
`amral-research-trees/collatz-verification-zhuiheng/`, which settles the finite
half by exact integer arithmetic; the queue that decides what lands here is
[`reports/LEAN-QUEUE.md`](../../amral-research-trees/collatz-verification-zhuiheng/reports/LEAN-QUEUE.md)
in that tree.

## What is proved

[`Collatz/AllOnes.lean`](./Collatz/AllOnes.lean) — **the finite-local no-go**
(Round 03-A.5 §5–§6), the cheapest entry in the queue and the one with the most
leverage, because it is a statement about *proof methods*.

- `orbit_allOnes` — the orbit of `2^(m+1) - 1` satisfies `Y i + 1 = 3^i · 2^(m+1-i)`
  for every `i ≤ m`. Stated without natural subtraction, which is where the
  proof's difficulty would otherwise have gone.
- `kappa_allOnes` — every one of the first `m` accelerated exponents is exactly `1`.
- `K_allOnes`, `subcritical_allOnes` — cumulative exponent `m`, and subcriticality
  at every prefix as the **integer** statement `2 ^ K_j < 3 ^ j`. No real numbers
  appear: `K_j < j log₂ 3` is equivalent to it.
- `occupancy_allOnes`, `finite_local_no_go`, `arbitrarily_long_zero_occupancy` —
  arbitrarily long zero-occupancy subcritical prefixes exist, so **no finite
  forbidden-pattern argument can finish the A line.**

The finite arm had verified all of this to `m = 40`. Instantiation was never the
claim; what is added here is the quantifier.

## What is checked about the proofs

```bash
lake env lean Collatz/Audit.lean
```

Prints `#print axioms` for all seven theorems — each depends only on `propext`,
`Classical.choice`, `Quot.sound`, so there is no `sorry` and no added axiom — and
evaluates concrete values, including a start (`n = 27`) whose occupancy is
**positive**. Without that last one the no-go would be a statement about a
quantity that cannot be positive.

```bash
python gate/crosscheck_against_finite_arm.py
```

Confronts `Collatz.orbit` / `Collatz.kappa` with the finite arm's
`hz_accel_code.accel_code` / `orbit_endpoints`, which were written from Round
03-A.1's prose and never from this development. 6 starts, 83 exponent values and
83 orbit values, elementwise. It carries a disagreement control, because a
comparison that cannot report a mismatch is not evidence.

## Building

```bash
lake exe cache get
```

```bash
lake build
```
