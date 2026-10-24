import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A C2 two-parameter variation in a real normed space and a C2 energy where used.
* **Objects:** Variation velocity, variation field and the equality of mixed derivatives.
* **Proof detail:** Represent both partial derivatives by the total derivative on coordinate vectors; apply symmetry of the second Fréchet derivative and compose base-energy differentials.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** These are Banach-space calculus consequences of C2 mixed-derivative symmetry; the source book treats the finite-dimensional version.
-/

/-!
# Actual derivatives of a two-parameter variation

For a C2 map `σ : ℝ × ℝ → E` on an open parameter domain, the time velocity and
variation field are defined using the actual ordinary derivatives of its slices.
They agree with evaluations of the joint Fréchet derivative in the two coordinate
directions. This gives C1 regularity of the velocity and of each variation field.

The mixed-derivative theorem differentiates these identities on neighborhoods supplied
by openness, then applies symmetry of the actual second Fréchet derivative. Thus the
parameter derivative of velocity is the time derivative of the variation field; no
mixed-derivative identity is assumed. Two final lemmas give C1 regularity of the actual
base energy differential of a C2 scalar energy, complementing the existing momentum API.

All results hold in an arbitrary real normed model space, without finite dimensionality,
completeness, an inner product, convexity, or an equation for the reference curve.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual time derivative of a two-parameter variation. -/
def variationVelocity (σ : ℝ × ℝ → E) (z : ℝ × ℝ) : E :=
  deriv (fun t ↦ σ (z.1, t)) z.2

/-- The actual variation derivative along a fixed parameter slice. -/
def variationField (σ : ℝ × ℝ → E) (s₀ t : ℝ) : E :=
  deriv (fun s ↦ σ (s, t)) s₀

/-- Time-slice differentiation is evaluation of the actual joint differential. -/
theorem variationVelocity_eq_fderiv {σ : ℝ × ℝ → E} {z : ℝ × ℝ}
    (hσ : DifferentiableAt ℝ σ z) :
    variationVelocity σ z = fderiv ℝ σ z (0, 1) := by
  exact (hσ.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

/-- Parameter-slice differentiation is evaluation of the actual joint differential. -/
theorem variationField_eq_fderiv {σ : ℝ × ℝ → E} {s t : ℝ}
    (hσ : DifferentiableAt ℝ σ (s, t)) :
    variationField σ s t = fderiv ℝ σ (s, t) (1, 0) := by
  exact (hσ.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))).deriv

/-- The actual velocity of a C2 variation is C1 on its open parameter domain. -/
theorem contDiffOn_variationVelocity {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) :
    ContDiffOn ℝ 1 (variationVelocity σ) D := by
  have h := (hσ.fderiv_of_isOpen hD (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
    (contDiffOn_const (c := (0, 1)))
  apply h.congr
  intro z hz
  exact variationVelocity_eq_fderiv
    ((hσ.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num))

/-- The actual variation field is C1 on the open time slice. -/
theorem contDiffOn_variationField {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) (s₀ : ℝ) :
    ContDiffOn ℝ 1 (variationField σ s₀) {t | (s₀, t) ∈ D} := by
  have h := (hσ.fderiv_of_isOpen hD (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
    (contDiffOn_const (c := (1, 0)))
  have hc := h.comp (contDiffOn_const.prodMk contDiffOn_id)
    (show MapsTo (fun t : ℝ ↦ (s₀, t)) {t | (s₀, t) ∈ D} D from fun _ ht ↦ ht)
  apply hc.congr
  intro t ht
  exact variationField_eq_fderiv
    ((hσ.contDiffAt (hD.mem_nhds ht)).differentiableAt (by norm_num))

/-- Parameter differentiation of the actual velocity equals the time derivative of the
actual variation field. Mixed equality is proved from the C2 joint derivative symmetry. -/
theorem hasDerivAt_variationVelocity {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ t : ℝ} (hz : (s₀, t) ∈ D) :
    HasDerivAt (fun s ↦ variationVelocity σ (s, t))
      (deriv (variationField σ s₀) t) s₀ := by
  have hσ₂ := hσ.contDiffAt (hD.mem_nhds hz)
  have hd := (hσ₂.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hds := hd.comp_hasDerivAt s₀
    ((hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ t))
  have hdt := hd.comp_hasDerivAt t
    ((hasDerivAt_const t s₀).prodMk (hasDerivAt_id t))
  have hvs : HasDerivAt (fun s ↦ variationVelocity σ (s, t))
      (fderiv ℝ (fderiv ℝ σ) (s₀, t) (1, 0) (0, 1)) s₀ := by
    have hh := hds.clm_apply (hasDerivAt_const s₀ (0, 1))
    simp only [ContinuousLinearMap.map_zero, add_zero] at hh
    apply hh.congr_of_eventuallyEq
    have hn : ∀ᶠ s in 𝓝 s₀, (s, t) ∈ D :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hD.mem_nhds hz)
    filter_upwards [hn] with s hs
    exact variationVelocity_eq_fderiv
      ((hσ.contDiffAt (hD.mem_nhds hs)).differentiableAt (by norm_num))
  have hwt : HasDerivAt (variationField σ s₀)
      (fderiv ℝ (fderiv ℝ σ) (s₀, t) (0, 1) (1, 0)) t := by
    have hh := hdt.clm_apply (hasDerivAt_const t (1, 0))
    simp only [ContinuousLinearMap.map_zero, add_zero] at hh
    apply hh.congr_of_eventuallyEq
    have hn : ∀ᶠ τ in 𝓝 t, (s₀, τ) ∈ D :=
      (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hz)
    filter_upwards [hn] with τ hτ
    exact variationField_eq_fderiv
      ((hσ.contDiffAt (hD.mem_nhds hτ)).differentiableAt (by norm_num))
  apply hvs.congr_deriv
  rw [hwt.deriv]
  exact (hσ₂.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, 1)

/-- A C2 energy has a C1 actual base differential. -/
theorem contDiffAt_baseEnergyDifferential_one_of_two {L : E × E → ℝ} {z : E × E}
    (hL : ContDiffAt ℝ 2 L z) : ContDiffAt ℝ 1 (baseEnergyDifferential L) z := by
  have h : ContDiffAt ℝ 2 (fun p : (E × E) × E ↦ L (p.2, p.1.2)) (z, z.1) :=
    hL.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact h.fderiv contDiffAt_fst (by norm_num)

/-- On an open C2 energy domain, the actual base differential is C1. -/
theorem contDiffOn_baseEnergyDifferential_one_of_two {L : E × E → ℝ}
    {U : Set (E × E)} (hU : IsOpen U) (hL : ContDiffOn ℝ 2 L U) :
    ContDiffOn ℝ 1 (baseEnergyDifferential L) U := by
  intro z hz
  exact (contDiffAt_baseEnergyDifferential_one_of_two
    (hL.contDiffAt (hU.mem_nhds hz))).contDiffWithinAt

end OTSelector.Geometry
