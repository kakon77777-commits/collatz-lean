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

### Paper 07, the generalised `mx + r` atlas — [`Collatz/Generalized.lean`](./Collatz/Generalized.lean)

Strip `3` and `1` out of the branches: `D x = x/2`, `U_{m,r} x = (mx+r)/2` with
`m, r` odd. Paper 07 claims the whole finite-word algebra survives, and §6 says
`(m,r) = (3,1)` "immediately recovers Paper 02".

**That last claim is the reason this item follows Paper 02, and it is proved
here rather than remarked.** `bG_three_one` and `FG_three_one` show the
generalised correction and operator *are* Paper 02's — the two are defined
independently, neither definition mentioning the other.

| theorem | statement |
|---|---|
| `odd_branch_integral` | `m, r, n` odd ⟹ `2 ∣ mn + r`: the odd branch stays integral with no admissibility hypothesis |
| `affine_closure_G` | `F^{(m,r)}_w(x) = (m^{u(w)}x + b_w)/2^{|w|}` |
| `bG_append`, `bG_append_D/U` | concatenation and the recurrence `b_{wU} = m·b_w + r·2^{|w|}` |
| `bG_factor_r` | `b^{(m,r)}_w = r · b^{(m,1)}_w` — §33's "`r` only changes the finite geometry", made precise |
| `bG_closed_form` | `b_w = r Σ_t 2^{j_t−1} m^{u−t}` |
| `bG_three_one`, `FG_three_one` | the specialisation back to Paper 02 |
| `odd_pow_ne_two_pow` | for odd `m > 1` and `p > 0`, `m^p ≠ 2^q` |
| `alpha_irrational` | §25: `α_m = log_m 2` is irrational for every odd `m > 1` |

§25 is the first place in this development where real numbers are unavoidable,
and it is instructive how little of it is analysis: the content is the integer
statement that an odd power is never a power of two, and irrationality follows
in a few lines. The integer core is proved first and stands alone.

### Paper 03, residue cylinders — [`Collatz/ResidueCylinder.lean`](./Collatz/ResidueCylinder.lean)

Paper 02 closed the *algebra* of a parity word but left its **domain** open:
which integers actually follow `w`? Paper 03's answer is that they are exactly
one residue class mod `2^{|w|}`, so `{D,U}^k` corresponds to `ℤ/2^kℤ`.

| theorem | statement |
|---|---|
| `parityWord_add_odd_mul` | adding `c·2^k` for **odd** `c` leaves the first `k` branches alone |
| `parityWord_eq_iff_modEq` | two integers follow the same length-`k` word **iff** they are congruent mod `2^k` |
| `residues_injective`, `residues_surjective` | the `2^k` residues give `2^k` distinct words |
| `cylinder_has_positive_member` | every non-empty cylinder contains a positive integer |
| `iterate_eq_F` | after `k` steps the value is `F_w(n)` for `n`'s own word — the bridge from `ℕ` dynamics to `ℚ` algebra |
| `cylinder_congruence` | `2^k ∣ 3^{u(w)}·n + b_w`, which is what makes `r_w ≡ −b_w·3^{−u}` well posed |
| `transport` | §12: the affine operator carries `r + 2^k a` to `m + 3^u a` |
| `local_identity` | §16: in the two charts the operator **is** the identity on `ℤ` |
| `local_identity_dynamical` | the same for `T^k` on the positive domain |
| `exact_recovery` | §18: the source is recovered from the target with no loss |
| `cyl_injective`, `prog_injective` | §19: the trivialization loses nothing |

The charts are `φ_w(n) = (n − r_w)/2^k` and `ψ_w(y) = (y − m_w)/3^u`, so they
live on `ℤ` — subtraction is essential and `ℕ` is the wrong home. And §16's first
display is about the **formal** operator on the whole cylinder; only its
restriction is about `T^k` on the positive domain. Both are proved, in that
order, and `m_w` is never defined by a division: it is any integer with
`2^k·m = 3^u·r + b_w`, which is what §4 establishes and what the `r_w = 0` repair
was needed for. That keeps every proof in this section a ring identity.

**Two places where the obvious version is wrong, and one is the series' own
recorded correction:**

- **Periodicity is not `parityWord (n + 2^k) k = parityWord n k` by naive
  induction.** The `U` branch sends `n + c·2^k ↦ T n + 3c·2^{k−1}`, so the
  multiplier is *multiplied by 3* rather than preserved. Fixing `c = 1` gives an
  induction hypothesis too weak to apply to its own successor; quantifying over
  all odd `c` closes it.
- **The `r_w = 0` boundary.** The series' `AUDIT_AND_CORRECTIONS.md` records that
  Paper 03's original induction used `r_w ∈ Ω_w`, which fails for the all-`D`
  cylinder because its canonical residue is `0` and the domain is the *positive*
  integers. The theorem was never false; the proof needed the always-positive
  representative `r_w + 2^k`. Here that repair is
  `cylinder_has_positive_member`, stated for every cylinder rather than patched
  onto the one that breaks.

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

The generalised atlas is checked the same way against `compose(word, m, r)`:
**3,066 comparisons** over six parameter pairs — including `m = 1`, which §19
says needs separate understanding, and `r = 7`, because a parameter that only
ever appears as `1` is not being tested. A fifth control requires the six pairs
to give six genuinely different corrections, or the comparison would be one
function checked against itself six times.

Paper 03's parity words are checked against the finite arm's own iteration for
**every integer below `2^k`** at each depth up to 9 — 1,023 integers — with two
further controls: the residues must give `2^k` distinct words (otherwise the
bijection would be false and the comparison would still pass) and periodicity
must hold beyond the sampled range.

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
