# Collatz — a Lean 4 development

[![build and audit](https://github.com/kakon77777-commits/collatz-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kakon77777-commits/collatz-lean/actions/workflows/lean_action_ci.yml)

Machine-checked results from the Collatz work of **Neo.K (許筌崴)**, formalised
by the verification arm 數學戰士「墜衡」 / AMRAL Research Lab.

Lean 4 + mathlib, pinned in [`lean-toolchain`](./lean-toolchain) and
[`lake-manifest.json`](./lake-manifest.json).

> **This repository does not claim the Collatz conjecture, or any progress
> toward deciding it.** It formalises a small number of `∀`-quantified
> statements that a finite computation cannot settle, and one of them is a
> statement about *proof methods* rather than about numbers. What is and is not
> claimed is spelled out below.

## What is proved

### The finite-local no-go — [`Collatz/AllOnes.lean`](./Collatz/AllOnes.lean)

The all-one accelerated exponent code is subcritical at every prefix and is
realized by the concrete integer `2^(m+1) − 1`. Therefore arbitrarily long
zero-occupancy subcritical prefixes exist, and **no finite forbidden-pattern
argument can settle the line of attack this comes from**: whatever finite pattern
of exponents you forbid, a genuine positive integer avoids it for as long as you
like.

| theorem | statement |
|---|---|
| `orbit_allOnes` | `Y i + 1 = 3^i · 2^(m+1−i)` for every `i ≤ m` |
| `kappa_allOnes` | every one of the first `m` accelerated exponents is exactly `1` |
| `K_allOnes` | the cumulative exponent after `m` steps is `m` |
| `subcritical_allOnes` | `2 ^ K_j < 3 ^ j` at every prefix |
| `kappa_at_m_ge_two` | the run of ones ends **exactly** at `m` — sharp, not merely sufficient |
| `occupancy_allOnes` | the witness has zero occupancy over its whole prefix |
| `finite_local_no_go` | no positive `g` bounds occupancy below for every start |
| `arbitrarily_long_zero_occupancy` | the witness form of the same statement |

Two modelling choices kept the development elementary, and both are reusable:

- The subcriticality condition `K_j < j·log₂3` is stated as the **integer**
  statement `2 ^ K_j < 3 ^ j`. **No real numbers appear anywhere.**
- The orbit invariant is stated as `Y i + 1 = 3^i · 2^(m+1−i)` rather than
  `Y i = … − 1`, which keeps natural-number subtraction out of the induction.

### Paper 02, the finite-word affine atlas — [`Collatz/AffineAtlas.lean`](./Collatz/AffineAtlas.lean)

Every finite parity word acts on `ℚ` as **one** affine map, so a `k`-step branch
history compresses to the triple `(k, u, b_w)`. All six of the paper's theorems,
for all words:

| theorem | statement |
|---|---|
| A `affine_closure` | `F_w(x) = (3^{u(w)}·x + b_w) / 2^{|w|}` for every `x ∈ ℚ` |
| B `bCorr_append_D/U` | `b_{wD} = b_w`, `b_{wU} = 3b_w + 2^{|w|}` |
| C `bCorr_closed_form` | `b_w = Σ_t 2^{j_t−1} 3^{u−t}` over the positions of the `U`s |
| D `bCorr_append` | `b_{wv} = 3^{u(v)} b_w + 2^{|w|} b_v` |
| E `M_append` | word concatenation becomes matrix multiplication |
| F `bCorr_lower/upper` | `3^u − 2^u ≤ b_w ≤ 2^{k−u}(3^u − 2^u)` |

Two places where the honest statement is not the tidy one:

- **Theorem E multiplies in the opposite order to reading.** A word runs left to
  right, so `F_w = σ_k ∘ ⋯ ∘ σ₁` and therefore `M_{wv} = M_v · M_w`. The paper
  says this in §16; stating it the other way round would have looked neater and
  been false.
- **Theorem F is stated subtraction-free** (`3^u ≤ b_w + 2^u` and
  `b_w + 2^k ≤ 2^{k−u}·3^u`) because `b_w` lives in `ℕ`. `extremes_attained`
  shows both bounds are reached, so it is sharp rather than merely true.

`b_w` is *defined* by the recursion `List` itself recurses on, and the paper's
right-append recurrence is then **proved** as a corollary of Theorem D. Defining
it the paper's way and recursing the other way would have buried the content in
list-reversal lemmas.

## Why you should not simply believe the green badge

A Lean file that compiles proves its theorems *relative to what it assumes and
how its definitions are written*. There are well-known ways to make a green
build mean nothing, so this repository audits for them mechanically and the
audits run in CI. You do not have to take the author's word for any of it — you
can run each of these yourself.

**1. Nothing is assumed away.**

```bash
python gate/audit_axioms.py
```

Refuses `sorry`, any `axiom` declaration of our own, `native_decide` (which
discharges goals through the compiler rather than the kernel), `unsafe`,
`@[implemented_by]`, `@[extern]` and `partial def`; and requires every theorem's
axiom set to be contained in Lean's own three — `propext`, `Classical.choice`,
`Quot.sound`. It also refuses to pass if a theorem exists in the sources that no
`#print axioms` covers, because an audit that simply does not look at the new
theorem is worthless.

**2. The audit can fail.**

```bash
python gate/audit_drill.py
```

Plants six ways of cheating — a `sorry`, a private axiom, a `native_decide`, a
`partial def`, a theorem added without an audit line, and an audit line deleted —
and requires the audit to report each **for the reason named**. An audit nobody
has seen fail is a green light with no bulb behind it. It also verifies the
sources are restored byte-exactly afterwards.

**3. The definitions are the right objects.**

```bash
python gate/crosscheck_against_finite_arm.py
```

This is the one that matters most, and it is the one a reader is least likely to
check by hand. `Collatz.orbit` and `Collatz.kappa` are confronted with an
independent implementation of the same accelerated map — `hz_accel_code.py` in
[`amral-research-trees`](https://github.com/kakon77777-commits/amral-research-trees),
written from the source papers' prose and never from this development. Six
starts, 83 exponent values and 83 orbit values, elementwise.

For the affine atlas it goes further and is **exhaustive**: every word of length
at most 10 — **2,047 words** — with both `u(w)` and `b_w` compared against
`compose_affine`, which applies the branch maps one at a time straight off their
definitions and knows nothing about `b_w`. Lean emits each word's own encoding
so the other side rebuilds the word rather than relying on both sides
enumerating in the same order; an agreement that came from a shared ordering
would prove nothing. Four controls guard it, including one requiring the offsets
to actually vary (855 distinct values at length 10 — otherwise "order determines
offset" would be a claim about a constant) and one requiring the encoding to
separate the words.

**4. The statements are not vacuous.**

```bash
lake env lean Collatz/Audit.lean
```

Prints every theorem's axioms and evaluates concrete values — including a start
(`n = 27`) whose occupancy is **positive**. Without that, `finite_local_no_go`
would be a statement about a quantity that cannot be positive, which is true and
worthless.

## What this does **not** establish

- **Not the Collatz conjecture**, and nothing bearing on whether it is true.
- **Not CASP** (the Critical Anchored Spine Problem) or any of the open
  `∀`-statements the source line reduces to. The finite-local no-go says a
  *method* cannot work; it says nothing about whether the conclusion holds.
- **Not a claim that the underlying papers are correct.** This repository
  formalises specific statements from them. Everything else in those papers is
  outside its scope, and the companion arm's reports say plainly which claims
  were checked, which were only instantiated, and which are open.

## Building

```bash
lake exe cache get
```

```bash
lake build
```

Take the mathlib cache rather than building it — the difference is twenty
seconds against CPU-hours.

## Provenance and companion work

The finite half of this project lives in
[`amral-research-trees/collatz-verification-zhuiheng`](https://github.com/kakon77777-commits/amral-research-trees),
which settles by exact integer arithmetic everything that is settleable on a
bounded domain, and keeps `reports/LEAN-QUEUE.md` — the ordered list of claims
that structurally require a proof assistant, and the reason each is on it. The
all-one witness family formalised here had been verified there to `m = 40`;
instantiation was never the claim, and what Lean adds is the quantifier.

Licensed Apache-2.0.
