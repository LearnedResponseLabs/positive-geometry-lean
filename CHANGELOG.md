# Changelog

This repository holds the Lean 4 formalizations of Learned Response Labs, one folder per project. This file records
each addition, newest first. The papers' results are proof candidates pending external review.

## 0.1.0 (2026-10-26): `conj43`

The first project: the formalization accompanying *Galashin's Conjecture 4.3 via a convex gradient*
(https://doi.org/10.5281/zenodo.23676807). The folder `conj43/` holds exactly the files of the Lean source supplement
deposited on Zenodo with the paper (version 2026-10-26, https://doi.org/10.5281/zenodo.23676891). What changed in the
paper and its Lean source since the version circulated in August 2026:

### The paper

**Corrections.** Places where the August text was wrong as written:
- The row-difference proposition assumed that the induced permutation has no fixed point, while the conjecture allows
  coloops. Coloops are now handled directly, and an identity on half-open arcs is restated so that it holds for them.
- The directed edge angle used the raw label difference, so the logarithm of its sine was undefined on wrapped edges.
  The text now uses the affine lift $\theta_{j+n}=\theta_j+\pi$ throughout.
- The extension of Galashin's Proposition 5.12 to collisions of non-crossing labels used a density argument that fails
  when the crossing graph is disconnected. The proof now applies Proposition 5.12 on the gauge slice, where Lemma 5.13
  makes it hold, and extends to the chamber by component shifts. Open-cell membership at collisions is now credited to
  Proposition 4.2 with Definition 1.8 and eq. (2.6), not to Theorem 6.9.
- A supporting strict inequality is restricted to its open interval, the shift corollary derives its bounded-affine type
  from looplessness, the claim that every strand is a coloop when the crossing graph is empty is corrected, and the
  graph-Laplacian sandwich (Corollary 29) now assumes at least one crossing edge.

**New results.**
- Corollary 31: each point of the gradient's image on the gauge slice has exactly one preimage there, the unique
  minimizer of the tilted potential.
- Corollary 32: the ordinary necklace coordinates embed the critical cell, with an explicit inverse.
- Corollary 33: the critical cell is a real-analytic embedded submanifold of the real open positroid variety, and the
  measurement map is a real-analytic diffeomorphism.
- Lemma 14 (a closed walk of total advance $n$ is simple) and a named lemma on half-open arcs.
- Remark 8: a proof candidate for cells with loops, outside what the paper claims.

**Exposition.** Twenty-seven figures, where the August text had none, several drawn from values computed in Lean; a
worked five-label example (Appendix B); Lemma 20 and Lemma 5 drawn on actual instances (Appendix E); the two proofs of the winding-one partition in a new order, the formalized
window induction first; and corrected citations to Postnikov and to Oh–Postnikov–Speyer. Statement numbers moved: the
partition is now Proposition 15 (was 8), the sharp cycle inequality Theorem 28 (was 20) and the Laplacian sandwich
Corollary 29 (was 21).

**Formal status.** Table 1 in Appendix A gives the formal status of each numbered result.

### The Lean source (`conj43/`)

123 frozen statements, all proved with only the standard axioms, each proof checked against its frozen statement by
the Lean Comparator. They cover:
- the cotangent cycle inequality and its sharp form;
- the row-difference identity;
- the winding-one partition and its cycle count, and the window lemmas as the paper states them;
- the assembled Hessian, the potential, its gradient and its convexity on the gauge slice, and the variational inverse;
- the combinatorial and slice parts of the component reduction (Lemma 5).

Lean constructs neither Galashin's measurement map nor the Muller–Speyer twist. So Theorem 1, Corollary 32 and the
measurement half of Lemma 5 are proved *conditionally*: their hypotheses stand for the cited results, and Appendix A of
the paper states each one in mathematical notation. Lean also transcribes Galashin's definitions and proves that the
paper's encodings agree with them.
