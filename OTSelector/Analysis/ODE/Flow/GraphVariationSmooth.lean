import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.GraphLength
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.Hamiltonian.IntegralCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphVariationSmooth.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphVariationSmooth`; the selected original proof blocks follow. -/
section

/-!
Conditions: A smooth nonautonomous field and a C2 actual solution family with the stated variational identity.

Objects: Smooth time dependence of the state and actual parameter variations, with the Finsler readout adapter.

Proof detail: Adjoin clock, state and variation into one autonomous smooth ODE, apply bootstrap regularity and project its components.

Sources: Gerald Teschl, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57); Gerald Teschl, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Derived autonomous-lift/bootstrap argument; no substitute parameter derivative is used.
-/

/-!
# Smooth time dependence of actual graph variations

A jointly C2 family solving a smooth nonautonomous ODE has smooth time slices and
smooth actual parameter variations. The tangent lift of the original field supplies
an autonomous smooth ODE for the time, state, and variation together. For a finite
parameter space this also gives smoothness of the entire parameter differential.
The Finsler consumer uses the original graph length and the same Legendre inverse.
No joint infinite smoothness of the family or smoothness of its variations is assumed.
-/

open Set Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C2 solution family's time slices and actual directional parameter variations are smooth.
The derivative equation is derived from the original ODE and equality of mixed derivatives. -/
theorem contDiffOn_nonautonomousFamily_slice
    {X : ℝ → E → E} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ (Function.uncurry X) U)
    {Ψ : W × ℝ → E} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s)) (X z.2 (Ψ z)) z.2)
    (w₀ : W) (hmap : ∀ t, (w₀, t) ∈ D → (t, Ψ (w₀, t)) ∈ U) :
    ContDiffOn ℝ ∞ (fun t ↦ Ψ (w₀, t)) {t | (w₀, t) ∈ D} ∧
      ∀ ξ : W, ContDiffOn ℝ ∞ (fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ ξ)
        {t | (w₀, t) ∈ D} := by
  let Y : (ℝ × E) × E → (ℝ × E) × E := fun z ↦
    ((1, X z.1.1 z.1.2), fderiv ℝ (Function.uncurry X) z.1 (0, z.2))
  have hY : ContDiffOn ℝ ∞ Y (U ×ˢ univ) := by
    have hf : ContDiffOn ℝ ∞ (fun z : (ℝ × E) × E ↦ X z.1.1 z.1.2)
        (U ×ˢ univ) := hX.comp contDiffOn_fst (fun _ hz ↦ hz.1)
    have hd := (hX.fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).comp
      (contDiffOn_fst (s := U ×ˢ (univ : Set E))) (fun _ hz ↦ hz.1)
    exact (contDiffOn_const.prodMk hf).prodMk
      (hd.clm_apply (contDiffOn_const.prodMk contDiffOn_snd))
  have hI : IsOpen {t | (w₀, t) ∈ D} :=
    hD.preimage (continuous_const.prodMk continuous_id)
  have hlift (ξ : W) : ContDiffOn ℝ ∞
      (fun t ↦ ((t, Ψ (w₀, t)), fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ ξ))
      {t | (w₀, t) ∈ D} := by
    apply contDiffOn_integralCurve_of_isOpen hY hI
      (fun t ht ↦ ⟨hmap t ht, mem_univ _⟩)
    intro t ht
    have hXt := (hX.contDiffAt (hU.mem_nhds (hmap t ht))).differentiableAt (by simp)
    have hpart := hXt.hasFDerivAt.comp (Ψ (w₀, t))
      (hasFDerivAt_prodMk_right t (Ψ (w₀, t)))
    have hvar := hasDerivAt_parameterVariation_of_nonautonomousODE hD hΨ hODE ht
      hpart.differentiableAt ξ
    have heq : fderiv ℝ (X t) (Ψ (w₀, t)) =
        (fderiv ℝ (Function.uncurry X) (t, Ψ (w₀, t))).comp
          (ContinuousLinearMap.inr ℝ ℝ E) := hpart.fderiv
    rw [heq] at hvar
    exact ((hasDerivAt_id t).prodMk (hODE (w₀, t) ht)).prodMk hvar
  exact ⟨(hlift 0).fst.snd, fun ξ ↦ (hlift ξ).snd⟩

/-- A genuine graph solution family and its full parameter differential are smooth along
an open time slice, for the same smooth inverse branch and original graph Lagrangian. -/
theorem contDiffOn_graphHamiltonianFamily_slice [FiniteDimensional ℝ W]
    {L : (ℝ × E) × E → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field L g z.2 (Ψ z)) z.2)
    (w₀ : W)
    (hp : ∀ t, (w₀, t) ∈ D → ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target) :
    ContDiffOn ℝ ∞ (fun t ↦ Ψ (w₀, t)) {t | (w₀, t) ∈ D} ∧
      ContDiffOn ℝ ∞ (fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀)
        {t | (w₀, t) ∈ D} := by
  let A : ℝ × (E × (E →L[ℝ] ℝ)) → (ℝ × E) × (E →L[ℝ] ℝ) :=
    fun z ↦ ((z.1, z.2.1), z.2.2)
  have hA : ContDiff ℝ ∞ A :=
    (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hfield := (GraphHamiltonian.contDiffOn_field hL hG).comp hA.contDiffOn
    (show MapsTo A (A ⁻¹' g.target) g.target from fun _ hz ↦ hz)
  have hs := contDiffOn_nonautonomousFamily_slice
    (g.open_target.preimage hA.continuous) hfield hD hΨ hODE w₀ hp
  exact ⟨hs.1, contDiffOn_clm_apply.mpr hs.2⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × E) M]
  [IsManifold 𝓘(ℝ, ℝ × E) ∞ M] {F : ContinuousFinslerNorm (ℝ × E) M}

/-- Actual Finsler graph phases and their actual parameter differentials are smooth in time.
Only joint C2 and the original same-branch field equation are required of the family. -/
theorem chartGraph_family_contDiffOn_slice [FiniteDimensional ℝ W]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {g : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hsub : g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × E) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.chartGraphLagrangian x₀) g z.2 (Ψ z)) z.2)
    (w₀ : W)
    (hp : ∀ t, (w₀, t) ∈ D → ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target) :
    ContDiffOn ℝ ∞ (fun t ↦ Ψ (w₀, t)) {t | (w₀, t) ∈ D} ∧
      ContDiffOn ℝ ∞ (fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀)
        {t | (w₀, t) ∈ D} :=
  contDiffOn_graphHamiltonianFamily_slice ((hF.contDiffOn_chartGraphLength x₀).mono hsub)
    hG hD hΨ hODE w₀ hp

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
