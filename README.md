# positive-geometry-lean

Lean 4 formalizations from [Learned Response Labs](https://learnedresponselabs.github.io), an independent research
program on the positive Grassmannian and its critical varieties. Each folder is one project: a self-contained Lean
project (with Mathlib) that accompanies a paper, with frozen statement files and the configurations that check the
proofs against them. The papers' results are proof candidates pending external review.

## Projects

| Folder | Paper | What is formalized | Version |
|---|---|---|---|
| [`conj43/`](conj43/) | *Galashin's Conjecture 4.3 via a convex gradient* ([10.5281/zenodo.23676807](https://doi.org/10.5281/zenodo.23676807)) | 123 frozen statements, all proved: the combinatorial and analytic steps of the argument, the paper's lemmas of the window induction and the component reduction, an interface with Lean transcriptions of Galashin's definitions, and the main theorem in a conditional form | 0.1.0, 2026-10-26; archived as [10.5281/zenodo.23676891](https://doi.org/10.5281/zenodo.23676891) |

More projects will be added here over the coming weeks, each in a folder of its own: the total-positivity library that
`conj43` draws on, and the general-cell dimer route. [`CHANGELOG.md`](CHANGELOG.md) records every addition.

## What "checked" means here

- **Frozen statements.** Each project has challenge files: its theorems, stated with the proofs left out.
- **The Comparator.** For each configuration, the Lean Comparator confirms that the solution proves exactly the frozen
  statement, replayed in Lean's default kernel, using only the axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Conditional theorems.** Some theorems take hypotheses that stand for published results Lean does not construct
  here. Each project's README lists them and what they stand for. A formal proof of a conditional theorem is not a
  formal proof of the paper's unconditional statement.
- **Reading editions.** Each released paper has a public reading edition that sets every statement of the paper beside
  the frozen Lean statement that checks it, or the source it rests on, with figures drawn from Lean's output. The
  edition for `conj43` is at
  [learnedresponselabs.github.io/editions/clh/](https://learnedresponselabs.github.io/editions/clh/).

How the work is produced and reviewed is described on the program's
[About page](https://learnedresponselabs.github.io/about.html).

## Building a project

Each folder pins its own toolchain and Mathlib revision, and its README gives the exact commands. For `conj43`, see
[*Reproducing the Lean check*](conj43/README.md#reproducing-the-lean-check); its Lean project is `conj43/lean/`.

## Licence and citation

Code is under Apache-2.0 (`LICENSE`); documentation and retained reports are under CC BY 4.0. Each project's
`RIGHTS.md` lists the sources it vendors: `conj43` includes four files of Per Alexandersson's LeanLGV (Apache-2.0), in
`conj43/lean/LGV/`.

To cite a project, cite its paper and the archive DOI of the version you used; both are in the table above.
