# Repository Guidelines

## Project structure

This repository contains the Lean 4 proof of deterministic empirical optimal
transport selection on general Finsler manifolds and its manuscript `main.tex`.
Read `research/SCOPE.md`, `research/STATUS.md` and `research/PROOF_GUIDE.md` before
changing the mathematical argument.

- `OTSelector/` groups reusable proofs by `Analysis`, `MeasureTheory`,
  `Probability`, `Finite`, `PointProcess`, `Geometry/Finsler`, `Transport`,
  `Topology` and `LinearAlgebra`, alongside retained domain constructions.
- `OTSelector.lean` imports the complete library. Area entry points permit
  smaller imports. `Transport/EmpiricalSelector` contains the general theorem;
  `OTSelector/Main.lean` retains the earlier uniform Euclidean model.
- `Verify.lean` audits transitive axiom dependencies.
- `research/` contains the public mathematical guides, proof skeletons,
  bibliographic catalog and source-bound verification manifest.
- `tools/proof_atlas/` contains optional local proof retrieval tools. Keep
  generated indexes, vectors and model files outside the repository.
- `vendor/` preserves supporting sources, their licenses and attribution.
- `.github/workflows/build-pdf.yml` builds the manuscript PDF.

## Build and verification

Use the Lean version in `lean-toolchain` and dependencies in `lakefile.toml`
and `lake-manifest.json`. From the repository root:

```sh
lake exe cache get
lake build
lake env lean Verify.lean
```

After Lean proof changes, run the full build and axiom audit. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Do not introduce `sorry` or
additional axioms. Reuse source-bound verification when the relevant inputs
have not changed; the publication baseline is `research/VERIFICATION.json`.

After manuscript changes, with TeX Live and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

Keep generated PDFs, build products, temporary files and credentials out of Git.

## Mathematical and Lean style

Follow surrounding Lean style: explicit imports, scoped namespaces and two-space
proof indentation. Use `UpperCamelCase` for modules and types, `lowerCamelCase`
for definitions and descriptive underscore-separated theorem names.

Organize modules by mathematical topic and dependencies. Keep theorem statements
and their final proofs together; expose reusable arguments as lemmas and put
long constructions in topic-local technical files or `Proofs/` directories.
Preserve useful independent mathematics and unrelated changes.

Add module documentation and declaration comments where they explain mathematical
intent. Reusable methods should state their conditions, typed objects, proof
steps and precise book or paper sections. Distinguish an exact cited result from
a local corollary, generalization or implementation adapter. Update the public
proof skeleton or mathematical-methods catalog when its interfaces change.

Preserve the coordinate convention in `OTSelector/Basic/Model.lean`: formal
points use `(height, mark)`, physical points use `(mark, height)`. Keep the general
theorem's assumptions, quantifiers and conclusion consistent with `main.tex`.

## Commits and pull requests

Use short imperative subjects such as `Prove calibrated Finsler derivative bounds`.
Keep changes focused. Describe affected mathematical claims and include the
verification commands and results. Include a PDF excerpt for significant layout
changes. Preserve third-party licenses, notices and attribution.
