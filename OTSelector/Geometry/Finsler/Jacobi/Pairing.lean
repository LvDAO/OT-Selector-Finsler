import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow

/-!
## Lemma skeleton

* **Conditions:** Two actual block-variational solutions with symmetric A and C. Generic conservation allows real normed spaces and within derivatives on a closed interval. The constructed Finsler flow instance uses finite-dimensional smooth strongly convex data.
* **Objects:** The canonical skew pairing omega((J1,P1),(J2,P2))=P2(J1)-P1(J2), and the actual initial-state flow derivative.
* **Proof detail:** Differentiate the bilinear evaluation pairing. Mixed B terms cancel; symmetry cancels the A and C terms. Zero derivative gives conservation in the interior, continuity includes endpoints, and continuous-dual separation gives injectivity.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 7, Definition 7.5 and Proposition 7.6, pp. 31–32.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 7.1, Proposition 7.10 and Example 7.11, pp. 33–34.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=33
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 11, p. 327, equation (11–3), Jacobi equation for a geodesic variation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=25

**Relationship to the sources:** This is an explicit vector–continuous-dual realization of Hamiltonian symplectic-form preservation. It proves phase pairing conservation, without claiming the full curvature Jacobi equation, transverse reduction, or a distance-Hessian interpretation.
-/

/-!
# Canonical pairing of actual Finsler flow variations

The actual position and covector variations preserve their canonical skew pairing.
This follows from the genuine Hamiltonian block equations and Hessian symmetry,
without an inner product or a presumed symplectic flow. The closed-interval result
includes both endpoints. A zero initial pairing propagates, but arbitrary initial
variations need not have zero pairing. Transverse reduction and distance-Hessian
identification remain separate geometric steps.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical skew pairing of two position-covector phase directions. -/
def canonicalPhasePairing (u v : E × (E →L[ℝ] ℝ)) : ℝ := v.2 u.1 - u.2 v.1

/-- Symmetry of the true Hamiltonian blocks makes the variation pairing stationary. -/
theorem hasDerivWithinAt_hamiltonian_pairing_zero
    {J₁ J₂ : ℝ → E} {P₁ P₂ : ℝ → E →L[ℝ] ℝ}
    {A : E →L[ℝ] (E →L[ℝ] ℝ)} {B : E →L[ℝ] E} {C : (E →L[ℝ] ℝ) →L[ℝ] E}
    {I : Set ℝ} {t : ℝ}
    (hJ₁ : HasDerivWithinAt J₁ (B (J₁ t) + C (P₁ t)) I t)
    (hP₁ : HasDerivWithinAt P₁ (-A (J₁ t) - (P₁ t).comp B) I t)
    (hJ₂ : HasDerivWithinAt J₂ (B (J₂ t) + C (P₂ t)) I t)
    (hP₂ : HasDerivWithinAt P₂ (-A (J₂ t) - (P₂ t).comp B) I t)
    (hA : ∀ u v : E, A u v = A v u)
    (hC : ∀ p q : E →L[ℝ] ℝ, q (C p) = p (C q)) :
    HasDerivWithinAt (fun s ↦ P₂ s (J₁ s) - P₁ s (J₂ s)) 0 I t := by
  convert! (hP₂.clm_apply hJ₁).sub (hP₁.clm_apply hJ₂) using 1
  simp only [sub_apply, neg_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [hA (J₂ t) (J₁ t), hC (P₁ t) (P₂ t)]
  ring

/-- Canonical pairing is conserved on the entire closed time interval. -/
theorem hamiltonian_pairing_eq_on_Icc
    {J₁ J₂ : ℝ → E} {P₁ P₂ : ℝ → E →L[ℝ] ℝ}
    {A : ℝ → E →L[ℝ] (E →L[ℝ] ℝ)} {B : ℝ → E →L[ℝ] E}
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hJ₁ : ∀ t ∈ Icc a b, HasDerivWithinAt J₁ (B t (J₁ t) + C t (P₁ t)) (Icc a b) t)
    (hP₁ : ∀ t ∈ Icc a b, HasDerivWithinAt P₁ (-A t (J₁ t) - (P₁ t).comp (B t))
      (Icc a b) t)
    (hJ₂ : ∀ t ∈ Icc a b, HasDerivWithinAt J₂ (B t (J₂ t) + C t (P₂ t)) (Icc a b) t)
    (hP₂ : ∀ t ∈ Icc a b, HasDerivWithinAt P₂ (-A t (J₂ t) - (P₂ t).comp (B t))
      (Icc a b) t)
    (hA : ∀ t ∈ Icc a b, ∀ u v : E, A t u v = A t v u)
    (hC : ∀ t ∈ Icc a b, ∀ p q : E →L[ℝ] ℝ, q (C t p) = p (C t q)) :
    ∀ t ∈ Icc a b, P₂ t (J₁ t) - P₁ t (J₂ t) =
      P₂ t₀ (J₁ t₀) - P₁ t₀ (J₂ t₀) := by
  let W : ℝ → ℝ := fun t ↦ P₂ t (J₁ t) - P₁ t (J₂ t)
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt W 0 (Icc a b) t :=
    hasDerivWithinAt_hamiltonian_pairing_zero (hJ₁ t ht) (hP₁ t ht)
      (hJ₂ t ht) (hP₂ t ht) (hA t ht) (hC t ht)
  have hd' (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt W 0 t :=
    (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have heq : EqOn W (fun _ ↦ W t₀) (Ioo a b) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs ↦ (hd' s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd' s hs).deriv) ht ht₀
  exact heq.of_subset_closure (fun t ht ↦ (hd t ht).continuousWithinAt)
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (ht₀.1.trans ht₀.2).ne])

/-- Preservation of the canonical pairing forces injectivity of a linear phase map. -/
theorem injective_of_canonicalPhasePairing_preserved
    (T : (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × (E →L[ℝ] ℝ)))
    (hT : ∀ u v, canonicalPhasePairing (T u) (T v) = canonicalPhasePairing u v) :
    Function.Injective T := by
  have hker (u : E × (E →L[ℝ] ℝ)) (hu : T u = 0) : u = 0 := by
    have hp (v : E × (E →L[ℝ] ℝ)) : canonicalPhasePairing u v = 0 := by
      rw [← hT u v, hu]
      simp [canonicalPhasePairing]
    have hx : u.1 = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero
      (fun p ↦ by simpa [canonicalPhasePairing] using hp (0, p))
    have hq : u.2 = 0 := by
      ext x
      simpa [canonicalPhasePairing] using hp (x, 0)
    exact Prod.ext hx hq
  intro u v huv
  exact sub_eq_zero.mp (hker (u - v) (by rw [map_sub, huv, sub_self]))

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- Genuine local Finsler flows have pairing-preserving, injective initial derivatives.
All flow and regularity data are constructed from the original Finsler structure. -/
theorem exists_chartHamiltonian_pairingFlow (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let p₀ := parametricLegendre L z
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T : ℝ) (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun q ↦ Φ (q, t)) p₀) ∧
      fderiv ℝ (fun q ↦ Φ (q, t₀)) p₀ = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u v : E × (E →L[ℝ] ℝ),
        canonicalPhasePairing (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ u)
          (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ v) = canonicalPhasePairing u v) ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        Function.Injective (fderiv ℝ (fun q ↦ Φ (q, t)) p₀) := by
  obtain ⟨e, r, T, Φ, he, hz', hsub, hG, hr, hT, hflow, hmap,
    hdiff, hinit, hstart, hvar, hblocks⟩ :=
    hF.exists_chartHamiltonian_variationalFlow x₀ hz t₀
  refine ⟨e, r, T, Φ, he, hz', hsub, hG, hr, hT, hflow, hmap, hdiff, hinit, ?_⟩
  have hpair : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u v : E × (E →L[ℝ] ℝ),
      canonicalPhasePairing
        (fderiv ℝ (fun q ↦ Φ (q, t)) (parametricLegendre (F.chartEnergy x₀) z) u)
        (fderiv ℝ (fun q ↦ Φ (q, t)) (parametricLegendre (F.chartEnergy x₀) z) v) =
      canonicalPhasePairing u v := by
    intro t ht u v
    have h := hamiltonian_pairing_eq_on_Icc
      (t₀ := t₀) (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
      (fun s hs ↦ (hvar u s hs).1) (fun s hs ↦ (hvar u s hs).2)
      (fun s hs ↦ (hvar v s hs).1) (fun s hs ↦ (hvar v s hs).2)
      (fun s hs ↦ (hblocks s hs).2.1) (fun s hs ↦ (hblocks s hs).2.2.1) t ht
    simpa only [canonicalPhasePairing, flowPositionVariation, flowMomentumVariation,
      hinit, ContinuousLinearMap.id_apply] using h
  exact ⟨hpair, fun t ht ↦ injective_of_canonicalPhasePairing_preserved _ (hpair t ht)⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
