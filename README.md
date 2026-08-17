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

### Paper 06, the valuation language — [`Collatz/Valuation.lean`](./Collatz/Valuation.lean)

A change of coordinates: instead of a parity word over `{D,U}`, an odd-to-odd
orbit is described by its **valuation word** `κ = (κ₁,…,κ_m)` with
`κ_i = v₂(3n_{i−1}+1)`, moved by the accelerated map `S(n) = (3n+1)/2^{κ(n)}`.

| theorem | statement |
|---|---|
| A `length_expand`, `uCount_expand` | `E(κ) = U D^{κ₁−1}⋯` has length `K` and `u = m` |
| C `bCorr_expand` | **the accelerated correction `B_κ` IS Paper 02's `b_w` of the expansion** |
| `Bcorr_append_right` | the paper's own recurrence `B_j = 3B_{j−1} + 2^{K_{j−1}}` |
| §6 `iterate_kappa`, `orbit_eq_iterate` | `m` accelerated steps are exactly `K = Σκ` modified steps |
| B `accelerated_affine_closure` | `2^K · S^m(n) = 3^m n + B_κ` |
| E `contraction_boundary` | `2^K > 3^m` — the integer form of `K/m > log₂3` |
| F `one_step_residue_unique`, `odd_residue_count` | `v₂(3n+1) = j` pins one residue mod `2^{j+1}`, of which `2^j` are odd |
| `S_odd`, `one_le_valWord` | the accelerated map preserves oddness, so `κ_i ≥ 1` is a fact and not an assumption |

**§14 claims a complete correspondence with Paper 02, and as with Paper 07's §6
that is a claim about a previous development — so it is proved.** `bCorr_expand`
and `orbit_eq_iterate` say the two papers describe the same object in two
coordinate systems: the same correction, and the same orbit re-indexed. Theorem B
is then proved by Paper 06's own induction anyway, so `bCorr_expand` stays an
independent statement rather than a step in it.

`S_odd` is the one place in the file that needs more than divisibility — it uses
the **maximality** of `v₂`, which is what makes `(3n+1)/2^{v₂}` odd.

### Paper 09, the stopping-time equivalence — [`Collatz/StoppingTime.lean`](./Collatz/StoppingTime.lean)

`σ(n) = inf{ j ≥ 1 : T^j(n) < n }`, and `Collatz ⟺ ∀ n > 1, σ(n) < ∞`.

| theorem | statement |
|---|---|
| `collatz_iff_finite_stopping` | Theorem A: the equivalence, both directions |
| `sigma_spec` | where `σ` is finite it is the **least** such `j`, so `Nat.find` is the paper's `inf` |
| **`reaches_one_of_bounded_stopping`** | verifying `σ(n) < ∞` on `[2, N]` proves Collatz on `[1, N]` — **and only there** |
| **`no_uniform_depth`** | §52: there is **no** `k` with `T^k(n) < n` for every `n > 1` |

**This is the item that says what a bounded computation is evidence for.** The
companion arm's exhaustive `[3, 2^40]` descent run is precisely a bounded
stopping-time verification, and `reaches_one_of_bounded_stopping` is what licenses
reading it as a statement about that interval. There is deliberately **no**
theorem bridging the bounded conclusion to the unbounded one: that gap is the
conjecture.

`no_uniform_depth` makes the other half precise. §52 warns that `∀n ∃k` must not
be swapped for `∃k ∀n`; that warning is a theorem, and its counterexample is the
all-ones family from the first file — `2^{k+1} − 1` has *grown* after `k` steps
(at `k = 6`: 127 ↦ 1457). So no computation of any fixed depth can establish the
hypothesis, however far it runs.

### Hard-Zeta, the `n ≥ 2` stopping domain — [`Collatz/HardSet.lean`](./Collatz/HardSet.lean)

The series' `AUDIT_AND_CORRECTIONS.md` records that a corrigendum had already
fixed the stopping-time domain to `n ≥ 2`, while the main body still wrote
`E_k^C = ⊔ H_w`; the corrected form is `H̃_w = H_w ∩ [2,∞)`, so that "the `n = 1`
boundary cannot silently re-enter through the Hurwitz-zeta representation".

| theorem | statement |
|---|---|
| `one_is_permanently_undescended` | **`1` never descends**, at any depth: `T^j(1) ∈ {1,2}` always |
| `one_not_hard`, `zero_not_hard` | so the `2 ≤ n` clause is what excludes both degenerate points |
| `hard_eq_iUnion`, `hardIn_disjoint` | `E_k^C = ⊔_{|w|=k} H̃_w` — a genuine partition, by parity word |
| `one_not_mem_hardIn` | and `1` is in none of the pieces, so it cannot re-enter through the decomposition either |
| `descent_iff_quotient` | descent at step `k` is a **linear inequality in the chart coordinate**: `m + 3^u·a < r + 2^k·a` |
| `quotient_slope_sign` | its slope is `2^k − 3^u`, and the sign of that is the whole classification |

**`1` is not awkward by convention — it is a fixed point of the two-cycle.**
Without the domain clause it would sit in *every* `E_k`, and a Dirichlet sum over
the hard set would carry a `1^{-s}` term at every depth. That is the correction's
actual content, and it is a theorem rather than a stipulation.

`descent_iff_quotient` is why the per-chart mass is exactly computable: whether
`n` has descended by step `k` is not a fact about `n` at all, but a half-line
condition on its chart coordinate.

### Hard-Zeta, the invariant-measure qualification — [`Collatz/InvariantLimit.lean`](./Collatz/InvariantLimit.lean)

The corrections file also records that saying a subsequential empirical limit
*must* produce an invariant object was too strong without a state space and
limit-passage assumptions, and made the route conditional on a compactification,
tightness, and enough regularity to pass dynamics to a weak limit.

**The sharpest way to formalise a hypothesis is to show what breaks without it.**

| theorem | statement |
|---|---|
| `singleton_eq_zero` | invariance under the successor map forces **every** atom of `ℕ` to measure zero |
| `succ_no_invariant_prob` | so that system has **no invariant probability measure at all** |
| `invariant_prob_existence_is_a_hypothesis` | "an invariant probability measure exists" is not a theorem of measurable dynamics |
| `invariant_vanishes_on_finite` | and on `ℕ` the failure is not a normalisation artefact: any invariant measure vanishes on every finite set |

Without a hypothesis that keeps mass from escaping, the failure is not the mild
one — not "the limit might fail to be invariant", but that there is nothing for
it to converge *to*. That is why the qualification is load-bearing rather than
pedantic, and it is the same move as `no_uniform_depth`: turn the caution into a
theorem.

This is **not** Krylov–Bogolyubov, which mathlib does not have at this pin, and
weak convergence is not formalised — it does not need to be, because if no
invariant probability measure exists then no limit of any kind can be one.

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

Paper 06 is checked on **200 odd starts**: the valuation word, `K`, the
run-length expansion (against a Python re-implementation written from §5's prose)
and `B_κ` — the last compared against Paper 02's *own* composer applied to the
expansion, a route that never mentions `B` at all. 196 of the 200 words are
distinct, and a control requires that.

And the most direct anchor of all: **σ(n) for every `n` in `[2, 500)`** — 498
values — against the companion arm's own engine, the one that computed the
`[3, 2^40]` run. Max σ in that range is 59, across 24 distinct values, and a
control requires both that it varies and that it gets large.

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
