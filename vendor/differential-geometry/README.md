# DifferentialGeometry source attribution

Eight general ODE modules in `OTSelector/Analysis/ODE/Flow/` are adapted from
[qinz1yang/differential-geometry](https://github.com/qinz1yang/differential-geometry/tree/fd2f07fba4c6c102ba626c59153ad98da8f0d442),
commit `fd2f07fba4c6c102ba626c59153ad98da8f0d442`, under Apache-2.0.
The original license, notice and citation metadata are preserved here.

| Local file | Original path under `DifferentialGeometry/Analysis/ODE/Flow/` |
| --- | --- |
| `Variational.lean` | `LinearODE/Variational.lean` |
| `Defs.lean` | `Defs.lean` |
| `VariationalSolutionOperator.lean` | `C1Regularity/VariationalSolutionOperator.lean` |
| `FrechetDerivative.lean` | `C1Regularity/FrechetDerivative.lean` |
| `JointFrechetDerivative.lean` | `C1Regularity/JointFrechetDerivative.lean` |
| `ContDiffOnOne.lean` | `C1Regularity/ContDiffOnOne.lean` |
| `HigherRegularity.lean` | `HigherRegularity/FiniteOrder.lean` |
| `JointC2.lean` | `HigherRegularity/Variational/FiniteOrder.lean` |

Local changes: imports use the project paths; namespaces are flattened to
`OTSelector.Geometry.LocalFlow`; attribution and module comments were added.
The unused open-interval existence/uniqueness branch and its wrapper were removed
from the earlier selection. In `JointC2.lean`, the two terminal conditional
infinite-order theorems (original lines 1595–1657) were omitted; all finite-order
mechanisms and the unconditional joint C2 theorem were retained.
The retained mathematical statements and proof bodies are unchanged.

These modules prove local ODE existence and differentiation with respect to the
initial condition in real Banach spaces, with joint finite-order regularity in
finite dimensions. They impose no inner-product assumption. Project adapters
derive local bounds and apply joint C2 regularity to the same actual Finsler
Hamiltonian flow on its original open domain. The modules do not by themselves
prove the manifold selector.

The original `NOTICE` also describes upstream components outside this eight-file
selection. Those other components are not distributed by this source adaptation.
