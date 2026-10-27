# Source supplement to Galashin's Conjecture 4.3 via a convex gradient

Adam Guetz. Source supplement version 2026-10-26.

This is the coloop-inclusive Lean source accompanying the revised proof candidate *Galashin's Conjecture 4.3 via a
convex gradient* (the revision whose Appendix A names this supplement), together with two standalone finite checks. It
replaces the unpublished 2026-09-23 snapshot, which predates the analytic statements, the interface statements and the
frozen challenge files that the paper's Appendix A names, the 2026-10-16 snapshot, which predates the fourteen
statements of the sharp modulus, the first form of the cycle count and the shift, and the 2026-10-18 snapshot, which
predates the two statements of the inverse-Lipschitz bound and the three of loop deletion, and the 2026-10-22b snapshot,
whose statement of Corollary 31 was weaker (uniqueness only among the preimages that minimize) and in no Comparator
configuration, and the 2026-10-23 snapshot, which predates the thirty-two statements of the window lemmas, the ordinary
necklace minors and the component reduction. It differs from the fixed-point-free formalization in the earlier certificate archive
(10.5281/zenodo.21664478). The earlier manuscript is identified by 10.5281/zenodo.21650342. Neither earlier
identifier locates this supplement.

The proofs are machine-checked by Lean. The paper and its formal statements were reviewed internally before release;
external review is pending, and the paper's claims remain proof candidates until it has occurred. Packaging does not
change that status.

## Contents

| Path | What it is |
|---|---|
| `lean/` | The Lean project: modules, the frozen statement files, the Comparator configurations, build files, license; with the decorated-permutation adapter and the loop deletion from the companion package LeanTP |
| `lean/SOURCE_MANIFEST.json` | Every Lean-tree file with its SHA-256 and origin, the pinned source revision, and the two files that differ from it |
| `checks/scripts/check_measurement_gradient.py` | Standalone NumPy checker of the measurement-to-gradient convention |
| `checks/scripts/validate_table_abstractions.py` | Standalone exhaustive check of the arithmetic abstractions behind the window-induction proof |
| `checks/retained/` | The retained receipt of the first checker |
| `MANIFEST.json`, `verify_manifest.py` | Payload digests and a read-only integrity check |
| `RIGHTS.md` | The code and documentation license split |

Everything here runs from this archive alone. No script imports a file outside it.

## Formal sources

`lean/SOURCE_MANIFEST.json` lists every exported Lean-tree file with its SHA-256 and origin, and pins the source revision
(`a18aa43f17ecc9bdb5746fba34664f93d3273a43` of the author's repository, tagged `lean-conj43-supplement-2026-10-26`). That
revision is also the last that changed a Lean statement or proof. The files are that revision's, byte for byte, with two
exceptions listed in the manifest: `lean/lakefile.toml` gains the library entries `LGV`, `TP`, `TPAdapter` and `TPLoops`, so that
Lake builds the companion modules in this tree, and `lean/comparator_adapter.json` is the adapter's entry of the companion package's
Comparator configuration. The files themselves are included, so access to that repository is unnecessary.

- `lean/Conj43/` holds the modules and proofs of the Lake package `Conj43`. One of them, `Conj43/VariationalPreimage.lean`,
  proves Corollary 31 of the paper: `Conj43.variational_gradient_preimage` states that every point of the gradient's
  image on a gauge slice has exactly one preimage there, and that it is the unique minimizer of the linearly tilted
  potential (with $a=0$ it is the corollary). It is not imported by the root module; its statement is frozen in
  `Challenge/GradientPreimage.lean`.
- Three further groups of `lean/Conj43/`, also outside the root module's imports: `WindowLemmas*.lean` proves Lemma 14
  and Lemmas 17–21 of the paper as stated there; `NecklaceEmbedding*.lean` proves Theorem 1 and Corollary 32 in the
  ordinary necklace minors, conditionally; `Reduction*.lean` proves Lemma 5, its measurement half conditionally.
- `lean/TP/`, `lean/TPAdapter/` and `lean/LGV/` hold the decorated-permutation adapter from the companion package
  `LeanTP`, at the same revision, with the modules it imports. Four of them, in `lean/LGV/`, are `LeanTP`'s vendored port
  of LeanLGV by Per Alexandersson (Apache-2.0); see `RIGHTS.md`. The five `lean/TP/LoopDelete*.lean` modules and their
  root `lean/TPLoops.lean` hold `LeanTP`'s loop deletion, at the same revision.
- `lean/Challenge/` holds the frozen statement files, with their proofs omitted:
  - `Conj43.lean`, the 43 statements of the original layers;
  - `Interface.lean`, `InterfaceCrossing.lean`, `InterfaceChords.lean`, `InterfaceRefined.lean` and
    `InterfaceExponent.lean`, the 23 interface statements;
  - `PartitionCount.lean`, the 2 statements of the cycle count;
  - `ExtensionsCount.lean`, `ExtensionsSharp.lean`, `ExtensionsSandwich.lean`, `ExtensionsShift.lean` and
    `ExtensionsLipschitz.lean`, the 16 statements of the extensions;
  - `CrossingAdapter.lean`, the 3 statements of the decorated-permutation adapter;
  - `Loops.lean`, the 3 statements of loop deletion;
  - `GradientPreimage.lean`, the statement of Corollary 31;
  - `WindowLemmas.lean`, the 11 statements of Lemma 14 and Lemmas 17–21, two of them controls;
  - `NecklaceEmbedding.lean`, the 6 statements of the ordinary-minor form of Theorem 1 and Corollary 32;
  - `Reduction.lean` and `ReductionSquare.lean`, the 14 statements of Lemma 5 and the 1 of its measurement half.

  Each `*Scaffold.lean` file is a byte-identical copy of its challenge file; the component reduction's two challenge
  files have none. Their proof placeholders (`sorry`, one per statement) are by design; the libraries prove all 123
  statements with no `sorry` (the word occurs there only in historical comments).
- The Comparator configurations name the statements and permit only the axioms `propext`, `Quot.sound` and
  `Classical.choice`: `lean/comparator.json` the 43, `lean/comparator_interface.json` the interface, the cycle
  count, the extensions, Corollary 31, the window lemmas and the ordinary necklace minors (fourteen groups, 59
  statements), `lean/comparator_reduction.json` the component reduction (two groups, 15 statements),
  `lean/comparator_adapter.json` the adapter's 3 and `lean/comparator_loops.json` the 3 of loop deletion. They are for use with the
  Comparator tool for Lean (installed separately; it is not part of this archive). The author's confined Comparator
  run of 2026-10-26 on this revision, over all nineteen groups (123 statements), passed. The 43-statement, adapter,
  loop-deletion, five extension, gradient-preimage, window-lemma, ordinary-minor and two component-reduction challenges,
  submitted as their own solutions, were rejected for their `sorry`. Earlier runs over the 43 statements, and the own
  runs of the gradient-preimage, window-lemma, ordinary-minor and component-reduction groups, also rejected a
  deliberately changed statement in each. The run records are not part of this archive.
- Comments in several modules cite scripts, notes or a manuscript section file that are not included; they are
  historical. The census and cross-validation producers read an exact-rational census outside this archive and are
  omitted. The retained report `lean/out/crossval_coloop.json` is their output, not a fresh run.

### What is proved

The 123 statements, in the order they were added:

1. **Combinatorial spine.** The cotangent cycle inequality; the row-difference identity on crossing columns; the
   cover of the crossing edges by cycles and the winding-one partition (by a window induction, not the paper's
   strand-diagram argument; the paper gives both); four facts about coloops (a coloop lies in no crossing, lies in
   every necklace row, and has zero rows in both sides of the row-difference identity).
2. **Full unordered-pair row difference.** The exponent table has a column for every unordered pair; the columns of
   pairs crossing in neither direction are zero, so `P D M = B` holds with all pair columns present.
3. **Layer 5: Hessian and hinge.** Cycle sums of lifted angles; the assembled Hessian is positive semidefinite with
   kernel exactly the vectors constant on crossing components; the hinge identity relating the complex bracket to
   `2 sin(delta)`.
4. **Layer 6: potential and convexity.** The potential and its coordinate gradient `B log sin(delta)`; the Hessian
   `B diag(cot delta) B^T` as a strict derivative; degree balance `B 1 = 0` from the cycle partition; invariance under
   component shifts; positive definiteness and strict convexity on the gauge slice; an injective gradient that is an
   open embedding into the image of `B`; the variational inverse; and a conditional end-to-end homeomorphism.
5. **Layer 7: the logarithmic form of Galashin's Proposition 5.12.** From that formula on necklace rows (all pairs),
   Lean derives `R o Meas = G` using the vanishing of non-crossing columns, the row-difference identity, the
   logarithmic hinge and the degree balance. The conditional homeomorphism theorem
   `gal512_measurement_homeomorphism` then has inverse `G^{-1} o R`, and `gal512_hypotheses_nonvacuous` shows its
   hypotheses jointly satisfiable (a model, not Galashin's objects).
6. **The interface with Galashin's definitions** (23 statements). Lean transcribes his definitions, in his labels
   `1, ..., n`: loopless bounded affine permutations, the affine necklace formula `I_r = {f(a) mod n : a < r <= f(a)}`, the
   refined boundary with its exit and entry points (his Definition 1.5), affine f-crossings and alignments, the classes
   `Mis` of his Section 5.4, and the exponent of his equation (5.8). Against these transcriptions Lean proves that the
   encoding is a bijection onto his loopless bounded affine permutations of every rank, never has a loop, and makes a fixed
   point exactly a coloop; that its necklace row `r` is his `I_{r+1}`; that the positions `5 s_p + 4` and `5 p + 1` order
   refined points as his boundary does, and the paper's half-open lemma and arc description hold on his refined boundary;
   that its crossings, alignments and `Mis` classes are his, and two strands cross in some direction exactly when their
   chords interleave; and that `pairExponent` is his exponent. The affine f-crossing is transcribed with `t = f^{-1}(q)`;
   the definition before his equation (3.2) prints `t := f^{-1}(p)`, repeating the first argument.
7. **The cycle count** (2 statements). A vertex list with no repeated vertex winds `n` times its number of wrapped edges
   (`winding_eq_wrapped`), so every winding-one partition has as many cycles as there are wrapped crossing edges
   (`partition_card`), the second form of the paper's cycle count.
8. **Decorated permutations** (3 statements, from `LeanTP`). The crossing edges of a decorated permutation, loops
   allowed, are those of the loopless lift of its underlying permutation, whatever the decoration
   (`TP.decCrossEdge_iff`, `TP.decCrossEdges_eq`), and the winding-one partition holds for every decorated permutation
   (`TP.dec_winding_one_partition`).
9. **The extensions** (16 statements).
   - **The first form of the cycle count:** `n` times the number of cycles of a winding-one partition is the total
     advance of the crossing edges, which is `n` times the number of wrapped ones (`partition_advance`,
     `crossEdges_advance`).
   - **The sharp modulus:** for `m >= 3` and `0 < eta <= pi/m`, the constant
     `kappa*_m(eta) = (cot eta - (m-1) cot((m-1) eta)) / m` is positive (`kappaStar_pos`) and, for `eta < pi/m`, below
     `tan((m-2) eta / 2)` (`kappaStar_lt_tan`). The cycle inequality `sum cot(alpha_i) d_i^2 >= kappa*_m(eta) sum d_i^2`
     holds for angles at least `eta` summing to `pi` and velocities summing to zero (`sharp_cot_cycle`), with equality at
     the paper's extremal pair (`sharp_cot_extremizer`).
   - **The two-sided bound:** `kappa*_{f,Z}(eta) L <= H(theta) <= cot(eta) L` as quadratic forms, with `L = B B^T`
     (`sharp_laplacian_sandwich`).
   - **The inverse-Lipschitz bound:** on a convex set where every crossing angle is at least `eta`, with `lambda` the
     least positive eigenvalue of `L`, the gradient is strongly monotone modulo component shifts,
     `kappa*_{f,Z}(eta) lambda |[theta - theta']|^2 <= <G(theta) - G(theta'), theta - theta'>`
     (`sharp_strong_monotone`), hence `|[theta - theta']| <= |G(theta) - G(theta')| / (kappa*_{f,Z}(eta) lambda)`
     in the quotient norm (`sharp_inverse_lipschitz`).
   - **The shift, combinatorial half:** `f_down(p) = f(p - 1)` is bounded, periodic and bijective with rank `k - 1`
     (`rank_sum`, `shift_bounds`, `shift_periodic`, `shift_bijective`, `shift_rank`); it stays at or above the identity
     exactly when `f` has no loop (`shift_self_le_iff`); and the electrical permutation of a matching on `2N >= 2`
     labels shifts to the Ising one (`elec_shift_eq_ising`).
10. **Loop deletion** (3 statements, from `LeanTP`). Deleting a loop `p` (a point with `f(p) = p`) of a bounded affine
    permutation `f` of period `n + 1` leaves a bounded affine permutation `f'` of period `n` (`TP.deleteLoop_bdd`) of the
    same rank `k` (`TP.affRank_deleteLoop`), and lowers the length by exactly `k`: `l(f) = l(f') + k`
    (`TP.affLength_deleteLoop`), the bookkeeping identity of the paper's remark on loops.
11. **The gradient preimage** (1 statement; Corollary 31 of the paper). On every gauge slice, each point of the gradient's
    image has exactly one preimage, and that preimage is the unique minimizer of the potential tilted by the point
    (`Conj43.variational_gradient_preimage`).
12. **The window lemmas** (11 statements; Lemma 14 and Lemmas 17–21 of the paper). A closed walk of at least two labels
    whose consecutive labels differ has total advance a positive multiple of `n`, and if that advance is `n` it repeats
    no label (`walk_advance_multiple`, `walk_simple_of_advance`). On a decorated bounded window: the residue
    permutation preserves the active positions; an adjacent active ascent exists, with the bounds of the paper, and
    swapping it gives a window; the swap adds exactly one inversion, so `mu(w) = C(n,2) - inv(w)` drops by one
    (`swap_measure_drop`); the edge set changes by the identity, a subdivision or a triangle, in the paper's three
    regimes; and the triangle winds once. Two controls show that the advance must be exactly `n` and that the swapped
    positions must be adjacent.
13. **The ordinary necklace minors** (6 statements; Theorem 1 and Corollary 32 of the paper, conditionally). Under the
    continuity and surjectivity of the measurement map, continuity and positivity of the ordinary necklace minors, and
    the logarithmic form of Proposition 5.12 for them up to a common constant, the measurement map is a homeomorphism
    with inverse `G^{-1}(-P D log Delta)` (`untwisted_measurement_homeomorphism`), and the necklace map into positive
    vectors modulo positive rescaling is a topological embedding, with that inverse for every positive representative
    (`necklace_conditional_embedding`). No hypothesis mentions the twist. The hypotheses are jointly satisfiable, and
    the logarithmic hypothesis cannot be dropped (`necklace_log_needed`).
14. **The component reduction** (15 statements; Lemma 5 of the paper). Erasing the strands outside a connected
    component of the crossing graph and relabeling the survivors in order gives a loopless bounded affine permutation
    whose crossings are those of the component, whose crossing graph is connected, and which has no fixed point when the
    component has two or more labels; admissibility splits over the components, and the gauge slice is homeomorphic to
    the product of the components' slices. Given a homeomorphism of the critical cell onto the product of the
    components' critical cells that intertwines the measurement maps (Galashin's Proposition 4.10), the measurement map
    is a homeomorphism exactly when every component's is (`reduction_homeomorphism_iff`). Three controls and a
    two-component fixture are among the fourteen.

What these statements say in mathematical notation, with the published results they stand for, is Appendix A of the
paper; for loop deletion, the paper's remark on loops.

### What is assumed

`gal512_measurement_homeomorphism` is **conditional**. Its four hypotheses (the paper's (H1) to (H4)), each with the
published statement it stands for (numbering as in the paper's bibliography entry for Galashin):

| Hypothesis in Lean | Paper | Stands for |
|---|---|---|
| `hMeas` | (H1) | The measurement map on the gauge slice is continuous: Proposition 5.1 (regularity on the complex slice), with Lemma 5.13 identifying its value at real slice points |
| `honto` | (H2) | The measurement map sends the slice onto the critical cell: Proposition 4.2, the paragraph after it, and the sentence after equation (4.3) |
| `hN` | (H3) | The logarithmic twisted-necklace map is continuous on the critical cell: the Muller-Speyer left twist is regular on the open positroid variety; the critical cell lies in it (Proposition 4.2 with Definition 1.8 and equation (2.6)); necklace minors do not vanish there (equation (2.4)) |
| `hlog` | (H4) | Proposition 5.12, equation (5.8), on the necklace rows, after taking the logarithm of the absolute value, up to a common additive constant per point; assumed on the whole slice including admissible collisions of non-crossing labels |

Lean constructs neither the measurement map, Galashin's curve, the boundary-measurement graphs, the left twist nor the
Grassmannian. So this is not a formal proof of the paper's main theorem: that Galashin's objects satisfy (H1) to (H4)
is what the hypotheses stand for, not something Lean shows.

The docstrings of `hMeas` in the frozen file and two modules read "Proposition 5.1 and Theorem 6.9". The mention of
Theorem 6.9 is historical and is not used: continuity needs Proposition 5.1 with Lemma 5.13, and open-cell membership
is Proposition 4.2 with Definition 1.8 and equation (2.6). The frozen file is left unchanged as the reference for the
statements; docstrings do not enter the statements that Comparator compares.

### What the formalization made explicit

Points the paper's text had left to the reader, now stated and proved:

- **All pair columns.** The paper's exponent table has a column for every unordered pair and says non-crossing columns
  vanish; the formal identity states and proves it, including the pairs crossing in neither direction.
- **Where the log formula is used.** (H4) is assumed on the whole gauge slice, collisions of non-crossing labels
  included; Lean does not derive it there from a formula on a dense locus by a continuity argument.
- **Degree balance.** In-degree equals out-degree at every vertex of the crossing graph, so `B 1 = 0` and the constant
  `log 2` contributed by each edge cancels.
- **Lifted angles.** `delta = theta_q - theta_p + pi [q < p]`; the cycle sum equals `pi` times the winding for every
  angle vector, with no admissibility hypothesis, because the wrapped-edge indicators sum to one on a winding-one cycle.
- **The gauge slice.** Anchors are the least label of each crossing component; the slice is nonempty for every anchor
  vector (also with coloops and for `n = 0`) and convex, and the Hessian is positive definite on its tangent space.
- **The codomain.** The inverse lands in the literal image of the incidence matrix; a linear isomorphism of that
  image with the tangent space is constructed, with no dimension count assumed (in the paper's count the nullity is the number of components and the rank is `n`
  minus it; no Lean dimension theorem is claimed).
- **Vertex-simple cycles.** The partition statement includes that each cycle repeats no vertex.
- **Constants.** The cyclic difference annihilates a common scalar, including for `n = 1`.
- **Coloops.** A fixed point is a coloop, never a loop; a coloop lies in every necklace row and in no crossing.

### What is not formalized

The measurement map and the twist (above), and so the inputs of the conditional statements; the homeomorphism of the
shift corollary; the strand-diagram proof of the partition (only the window induction is formal); the reduction of a
looped cell to the loopless theorem (only the three facts of loop deletion are formal); the real-analytic corollary; and
the hyperbolic-volume reading of the paper's appendix.

### Two differences from the paper's text

In the window induction the paper counts inversions (`mu(w) = C(n,2) - inv(w)`, Lemma 19 of the paper), while
the construction of the partition in `Conj43/WindowAscent.lean` terminates on the position-weighted lift sum
`sum_i i w_i` (`Window.measure`), which an `(a,b)`-swap with `a < b` and `w_a < w_b` lowers by `(b-a)(w_b - w_a)`. The
paper's measure and its drop are proved separately (`swap_measure_drop`). And `Conj43/SeedCover.lean` represents a
winding-one cycle as a sorted subset through `consecutiveEdges`. Both are proof-engineering choices for the same
statements.

## Reproducing the Lean check

With Elan/Lake installed, run from the `lean/` directory:

```sh
lake exe cache get
lake build
lake build Conj43.InterfaceProofs Conj43.InterfaceCrossingProofs Conj43.InterfaceChordsProofs \
  Conj43.InterfaceRefinedProofs Conj43.InterfaceExponentProofs Conj43.PartitionCountProofs TPAdapter.Crossing \
  Conj43.ExtensionsCount Conj43.ExtensionsSharp Conj43.ExtensionsSandwich Conj43.ExtensionsShift \
  Conj43.ExtensionsLipschitz TPLoops Conj43.VariationalPreimage Conj43.WindowLemmasProofs \
  Conj43.NecklaceEmbedding Conj43.Reduction Conj43.ReductionSquareProof
lake build Challenge Challenge.Interface Challenge.InterfaceCrossing Challenge.InterfaceChords \
  Challenge.InterfaceRefined Challenge.InterfaceExponent Challenge.PartitionCount Challenge.CrossingAdapter \
  Challenge.ExtensionsCount Challenge.ExtensionsSharp Challenge.ExtensionsSandwich Challenge.ExtensionsShift \
  Challenge.ExtensionsLipschitz Challenge.Loops Challenge.GradientPreimage Challenge.WindowLemmas \
  Challenge.NecklaceEmbedding Challenge.Reduction Challenge.ReductionSquare
lake env lean axioms.lean
```

The default target builds the 43 statements of the original layers; the second command builds the proofs of the other 80,
which the root module does not import, and the third the frozen statement files. The toolchain is
`leanprover/lean4:v4.33.0-rc1`, with Mathlib pinned by the included `lake-manifest.json` to
`79d0395a1825a6264ad5d269e35e60537518955e`. Fetching the toolchain and dependencies requires network access. Do not run
`lake update` to reproduce this snapshot. `axioms.lean` prints the axioms of the four original spine theorems; the
expected report contains only `propext`, `Classical.choice` and `Quot.sound`.

A fresh extraction of this version's archive, which differed from this one only in this README's record of the runs, was
built with these commands on 2026-10-26 (Lean v4.33.0-rc1 and the pinned Mathlib, Mathlib cache fetched). Each completed
without errors: `lake build` in 8,697 jobs, the second command in 8,761 and the third in 8,701. The warnings come from
style linters, deprecations and unused names, besides one `sorry` warning per statement in the frozen statement files (123
in all). `#print axioms` over all 123 theorem names in the five Comparator configurations reported only `propext`,
`Classical.choice` and `Quot.sound`. Those are not Comparator runs. The frozen statement files are not part of the default
build target.

## Finite checks

`checks/scripts/check_measurement_gradient.py` is a standalone NumPy checker. It compares actual curve measurement
followed by the left twist and logarithmic necklace coordinates with independently assembled `B log sin(delta)`, at two
generic configurations on every non-top loopless cell with 2 <= n <= 7. It also tests a reversed wrapped incidence
column and an omitted affine lift. Install the requirement in an environment of your choice, then run from this
supplement's root:

```sh
python3 -m pip install -r checks/requirements.txt
OPENBLAS_NUM_THREADS=1 python3 checks/scripts/check_measurement_gradient.py
```

This writes `checks/out/measurement_gradient.json`; the original receipt remains in
`checks/retained/measurement_gradient.json`. The recorded run used Python 3.14.6 and NumPy 2.4.6. Its elapsed time and
floating-point values need not reproduce byte-for-byte on another platform. It checked 11,770 points on 5,885 cells; all
10,546 points with crossing edges rejected both convention controls. These are finite floating-point checks, not theorem
proofs or collision checks.

`checks/scripts/validate_table_abstractions.py` needs only the Python standard library:

```sh
python3 checks/scripts/validate_table_abstractions.py
```

It checks, over hypothesis pools rather than only real windows, the arithmetic abstractions that the omega steps of the
window-induction proof rely on: 2,772 and 336 tuples for the two transition-table pools (`n` from 2 to 8), 274,456 for
the move lemma (moduli 2 to 14) and 784 for the fixed-label lemmas (`n` from 1 to 7); 278,348 tuples in all. It prints
`fails: 0` four times. It finishes in under
a second. It is finite corroboration of what Lean proves, not an addition to it.

`lean/out/crossval_coloop.json` is a retained definition-check report (5,912 loopless cells with `2 <= n <= 7`, 3,737 of
them with a coloop, all bit-identical to an exact-integer mirror), not a fresh run. Its producer is not included. It does
not establish the geometric interpretation of the formal predicates.

## Scope and integrity

`MANIFEST.json` records the SHA-256 and size of every payload file other than the manifest itself. Verify the downloaded
archive against the separately supplied `SHA256SUMS`, then run `python3 verify_manifest.py` in a fresh extraction. See
`RIGHTS.md` for the code/documentation license split.
