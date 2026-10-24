import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeLocality
import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CotangentChartPairing.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CotangentChartPairing`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual C2 chart change with its actual inverse derivative and cotangent lift.

Objects: Preservation of the canonical cotangent pairing and the corresponding Finsler momentum transition.

Proof detail: Differentiate the inverse-derivative lift, use the differentiated inverse identity and Hessian symmetry to cancel correction terms.

Sources: Ana Cannas da Silva, Section 2.4, Proposition 2.1 and Corollary 2.2, pp. 11–12 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=19); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Local C2/Banach pairing calculation generalizing the book’s smooth finite-dimensional cotangent-lift theorem.
-/

/-!
# Canonical pairing under actual cotangent chart changes

A coordinate map and its actual local inverse determine the cotangent lift. Its true
Fréchet derivative preserves the canonical vector-covector pairing: the second derivative
of the inverse branch is symmetric, so its two correction terms cancel. Actual Finsler
chart momentum transforms by this same lift, without an independent matrix or pairing
assumption.
-/

open Set Filter Function Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Transport a covector by the derivative of the specified actual inverse branch. -/
def cotangentLift (φ : E → G) (ψ : G → E) (z : E × (E →L[ℝ] ℝ)) :
    G × (G →L[ℝ] ℝ) := (φ z.1, z.2.comp (fderiv ℝ ψ (φ z.1)))

private theorem inverse_branch_fderiv_comp {φ : E → G} {ψ : G → E} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ (φ x))
    (hleft : ψ ∘ φ =ᶠ[𝓝 x] id) :
    (fderiv ℝ ψ (φ x)).comp (fderiv ℝ φ x) = ContinuousLinearMap.id ℝ E := by
  have hc := hψ.hasFDerivAt.comp x hφ.hasFDerivAt
  have hi : HasFDerivAt (ψ ∘ φ) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hleft
  exact hc.unique hi

private theorem fderiv_cotangentLift_apply {φ : E → G} {ψ : G → E}
    {z : E × (E →L[ℝ] ℝ)}
    (hφ : DifferentiableAt ℝ φ z.1) (hψ : ContDiffAt ℝ 2 ψ (φ z.1))
    (u : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (cotangentLift φ ψ) z u =
      (fderiv ℝ φ z.1 u.1,
        z.2.comp (fderiv ℝ (fderiv ℝ ψ) (φ z.1) (fderiv ℝ φ z.1 u.1)) +
          u.2.comp (fderiv ℝ ψ (φ z.1))) := by
  have hx := hφ.hasFDerivAt.comp z hasFDerivAt_fst
  have hD := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hp := (hasFDerivAt_snd (p := z)).clm_comp (hD.comp z hx)
  have h := (hx.prodMk hp).fderiv
  simpa only [cotangentLift, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_def,
    _root_.add_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply] using! congrArg (fun A ↦ A u) h

/-- The derivative of the actual cotangent lift preserves the canonical pairing.
The local inverse identity and actual C2 Hessian symmetry supply both cancellations. -/
theorem cotangentLift_fderiv_pairing {φ : E → G} {ψ : G → E}
    {z : E × (E →L[ℝ] ℝ)}
    (hφ : DifferentiableAt ℝ φ z.1) (hψ : ContDiffAt ℝ 2 ψ (φ z.1))
    (hleft : ψ ∘ φ =ᶠ[𝓝 z.1] id) (u v : E × (E →L[ℝ] ℝ)) :
    canonicalPhasePairing (fderiv ℝ (cotangentLift φ ψ) z u)
      (fderiv ℝ (cotangentLift φ ψ) z v) = canonicalPhasePairing u v := by
  have hcomp := inverse_branch_fderiv_comp hφ
    (hψ.differentiableAt (by norm_num)) hleft
  have hinv (w : E) : fderiv ℝ ψ (φ z.1) (fderiv ℝ φ z.1 w) = w := by
    exact congrArg (fun A : E →L[ℝ] E ↦ A w) hcomp
  rw [fderiv_cotangentLift_apply hφ hψ u, fderiv_cotangentLift_apply hφ hψ v]
  simp only [canonicalPhasePairing, _root_.add_apply,
    ContinuousLinearMap.comp_apply, hinv]
  rw [(hψ.isSymmSndFDerivAt (by norm_num)).eq
    (fderiv ℝ φ z.1 v.1) (fderiv ℝ φ z.1 u.1)]
  ring

/-- With genuine two-sided inverse germs, this lift is exactly inverse-derivative transport. -/
theorem cotangentLift_eq_inverse {φ : E → G} {ψ : G → E}
    {z : E × (E →L[ℝ] ℝ)}
    (hφ : DifferentiableAt ℝ φ z.1) (hψ : DifferentiableAt ℝ ψ (φ z.1))
    (hleft : ψ ∘ φ =ᶠ[𝓝 z.1] id) (hright : φ ∘ ψ =ᶠ[𝓝 (φ z.1)] id) :
    cotangentLift φ ψ z = (φ z.1, z.2.comp (fderiv ℝ φ z.1).inverse) := by
  have hx : ψ (φ z.1) = z.1 := hleft.eq_of_nhds
  have hφ' : DifferentiableAt ℝ φ (ψ (φ z.1)) := hx.symm ▸ hφ
  have hr := inverse_branch_fderiv_comp hψ hφ' hright
  rw [hx] at hr
  have hi := ContinuousLinearMap.inverse_eq hr (inverse_branch_fderiv_comp hφ hψ hleft)
  simp only [cotangentLift, hi]

/-- Smooth coordinate maps and a smooth specified inverse give a smooth cotangent lift. -/
theorem contDiffOn_cotangentLift {φ : E → G} {ψ : G → E} {U : Set E} {V : Set G}
    (hφ : ContDiffOn ℝ ∞ φ U) (hV : IsOpen V) (hψ : ContDiffOn ℝ ∞ ψ V)
    (hmap : MapsTo φ U V) :
    ContDiffOn ℝ ∞ (cotangentLift φ ψ) (U ×ˢ (univ : Set (E →L[ℝ] ℝ))) := by
  have hx := hφ.comp (contDiffOn_fst (s := U ×ˢ (univ : Set (E →L[ℝ] ℝ))))
    (fun _ hz ↦ hz.1)
  have hd := (hψ.fderiv_of_isOpen hV (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).comp hx
    (fun _ hz ↦ hmap hz.1)
  exact hx.prodMk (contDiffOn_snd.clm_comp hd)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem chartTransition_inverse_germ (old new : M) {x : E}
    (hx : x ∈ chartTransitionDomain old new) :
    chartTransition new old ∘ chartTransition old new =ᶠ[𝓝 x] id := by
  filter_upwards [(isOpen_chartTransitionDomain old new).mem_nhds hx] with y hy
  exact chartTransition_reverse old new hy

/-- The actual cotangent change between two manifold charts is smooth on the overlap. -/
theorem contDiffOn_chartCotangentLift (old new : M) :
    ContDiffOn ℝ ∞ (cotangentLift (chartTransition old new) (chartTransition new old))
      (chartTransitionDomain old new ×ˢ (univ : Set (E →L[ℝ] ℝ))) :=
  contDiffOn_cotangentLift (contDiffOn_chartTransition old new)
    (isOpen_chartTransitionDomain new old) (contDiffOn_chartTransition new old)
    (mapsTo_chartTransition old new)

/-- Actual chart cotangent derivatives preserve canonical pairing, with no extra geometric data. -/
theorem chartCotangentLift_fderiv_pairing (old new : M) {z : E × (E →L[ℝ] ℝ)}
    (hz : z.1 ∈ chartTransitionDomain old new) (u v : E × (E →L[ℝ] ℝ)) :
    canonicalPhasePairing
      (fderiv ℝ (cotangentLift (chartTransition old new) (chartTransition new old)) z u)
      (fderiv ℝ (cotangentLift (chartTransition old new) (chartTransition new old)) z v) =
        canonicalPhasePairing u v := by
  have hφ := (contDiffOn_chartTransition old new).contDiffAt
    ((isOpen_chartTransitionDomain old new).mem_nhds hz)
  have hψ := (contDiffOn_chartTransition new old).contDiffAt
    ((isOpen_chartTransitionDomain new old).mem_nhds (mapsTo_chartTransition old new hz))
  exact cotangentLift_fderiv_pairing (hφ.differentiableAt (by simp))
    (hψ.of_le (by simp)) (chartTransition_inverse_germ old new hz) u v

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The same cotangent chart lift carries the actual original energy momentum to its new
coordinate expression. Both covectors are actual fiber derivatives of the original energy. -/
theorem chartLegendre_cotangentLift (hF : F.IsSmoothStronglyConvex) (old new : M)
    {x v : E} (hx : x ∈ chartTransitionDomain old new) (hv : v ≠ 0) :
    cotangentLift (chartTransition old new) (chartTransition new old)
      (x, fiberLegendre (F.chartEnergy new) (x, v)) =
      (chartTransition old new x,
        fiberLegendre (F.chartEnergy old) (tangentLift (chartTransition old new) (x, v))) := by
  have hφ := (contDiffOn_chartTransition old new).contDiffAt
    ((isOpen_chartTransitionDomain old new).mem_nhds hx)
  have hx' := mapsTo_chartTransition old new hx
  have hψ := (contDiffOn_chartTransition new old).contDiffAt
    ((isOpen_chartTransitionDomain new old).mem_nhds hx')
  have hleft := chartTransition_inverse_germ old new hx
  have hright := chartTransition_inverse_germ new old hx'
  rw [cotangentLift_eq_inverse (hφ.differentiableAt (by simp))
    (hψ.differentiableAt (by simp)) hleft hright]
  have hdomain := mapsTo_chartTransition_energyDomain old new (show
    (x, v) ∈ chartTransitionDomain old new ×ˢ {w : E | w ≠ 0} from ⟨hx, hv⟩)
  have hL := (hF.contDiffOn_chartEnergy old).contDiffAt
    ((ContinuousFinslerNorm.isOpen_chartEnergyDomain old).mem_nhds hdomain)
  have he := fiberLegendre_eq_of_eventuallyEq
    (F.chartEnergy_eventuallyEq_chartTransition old new hx v)
  have hpull := fiberLegendre_pullbackEnergy (φ := chartTransition old new)
    (z := (x, v)) (hL.differentiableAt (by simp))
  have hp : fiberLegendre (F.chartEnergy new) (x, v) =
      (fiberLegendre (F.chartEnergy old) (tangentLift (chartTransition old new) (x, v))).comp
        (fderiv ℝ (chartTransition old new) x) := he.trans hpull
  rw [hp, ContinuousLinearMap.comp_assoc,
    (isInvertible_fderiv_chartTransition old new hx).self_comp_inverse]
  simp

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
