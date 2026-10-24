# OT-Selector-Finsler

[Manuscript](main.tex) and [Lean 4 proof](OTSelector/Transport/EmpiricalSelector/Carriers.lean)
of deterministic empirical optimal transport selection on Finsler manifolds.
Related: [OT-Selector](https://github.com/LvDAO/OT-Selector), for the uniform planar case.

## Main theorem

Let $`(M,F)`$ be a connected, complete, smooth, reversible, strongly convex
Finsler manifold of dimension $`d\ge6`$, with smooth positive volume $`m`$.
Let $`\mu=\rho_A m`$ and $`\nu=\rho_B m`$ be probability measures with Lipschitz
densities and disjoint compact supports $`A,B`$.
For independent iid samples, let $`\mu_n,\nu_n`$ be the empirical measures and
$`\mathrm{Opt}_n`$ their full set of optimal couplings for the length distance $`d_F`$.

There is a deterministic population-optimal coupling $`\pi_*`$, determined by
$`(F,\mu,\nu)`$, such that for every such sampling and every metric $`d_{\rm weak}`$
inducing weak convergence on probability measures on $`A\times B`$,

```math
\sup_{\gamma\in\mathrm{Opt}_n} d_{\rm weak}(\gamma,\pi_*)
\xrightarrow[n\to\infty]{\mathbb P^*} 0,
```

where $`\mathbb P^*`$ denotes outer probability.

## Verify

Install [Lean through elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/LvDAO/OT-Selector-Finsler.git
cd OT-Selector-Finsler
lake exe cache get
lake build
lake env lean Verify.lean
```

`Verify.lean` audits the proof's axiom dependencies.

## Paper

Build with TeX Live and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

Download **OT-Selector-Finsler-paper** from a successful
[PDF build](https://github.com/LvDAO/OT-Selector-Finsler/actions/workflows/build-pdf.yml).
