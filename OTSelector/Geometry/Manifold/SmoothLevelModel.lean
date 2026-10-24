import OTSelector.Geometry.Manifold.SmoothLevelChart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SmoothLevelModel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SmoothLevelModel`; the selected original proof blocks follow. -/
section

/-!
Conditions: A nonzero covector on R×V and a smooth scalar regular-level chart.

Objects: A model V parametrization of the level with its actual differential and local image.

Proof detail: Use rank-nullity to choose a linear equivalence V≃ker p, then precompose the kernel level chart and apply the chain rule.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55).
Relation: Finite-dimensional model-coordinate adapter for the regular-level theorem.
-/

/-!
# Smooth regular level charts in the spatial graph model

A nonzero covector on real times V has kernel dimension equal to dim V. A continuous
linear equivalence reparameterizes the actual implicit-function level chart by V,
retaining its smoothness, level identity, local image and injective true derivative.
No preferred nonzero covector component or supplied level chart is required.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The kernel of any nonzero covector on the graph model has the spatial dimension. -/
theorem finrank_graphCovector_ker (p : (ℝ × V) →L[ℝ] ℝ) (hp : p ≠ 0) :
    Module.finrank ℝ p.ker = Module.finrank ℝ V := by
  have hn : (p : (ℝ × V) →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hp
    exact ContinuousLinearMap.coe_injective h
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  rw [Module.finrank_prod, Module.finrank_self] at h
  omega

/-- Identify a regular level tangent space with the spatial model, without choosing
any nonzero coordinate component of its covector. -/
def graphCovectorKernelEquiv (p : (ℝ × V) →L[ℝ] ℝ) (hp : p ≠ 0) :
    V ≃L[ℝ] p.ker :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_graphCovector_ker p hp).symm

omit [FiniteDimensional ℝ V] in
/-- Reparameterizing a genuine level chart by a linear equivalence preserves its
open image, actual level identity and immersion derivative. -/
private theorem reparam_levelChart {E W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) {σ : W → E} {B : Set W} {U Ω : Set E}
    {f : E → ℝ} {a : E} {D : W →L[ℝ] E}
    (hB : IsOpen B) (h0 : 0 ∈ B) (hσ : ContDiffOn ℝ ∞ σ B)
    (hσ0 : σ 0 = a) (hmap : MapsTo σ B Ω)
    (hlevel : ∀ w ∈ B, f (σ w) = f a)
    (hD : HasFDerivAt σ D 0) (hDi : Function.Injective D)
    (hi : InjOn σ B) (himage : σ '' B = U ∩ {x | f x = f a}) :
    ∃ (B' : Set V) (σ' : V → E), IsOpen B' ∧ 0 ∈ B' ∧
      ContDiffOn ℝ ∞ σ' B' ∧ σ' 0 = a ∧ MapsTo σ' B' Ω ∧
      (∀ w ∈ B', f (σ' w) = f a) ∧
      HasFDerivAt σ' (D.comp e.toContinuousLinearMap) 0 ∧
      Function.Injective (fderiv ℝ σ' 0) ∧ InjOn σ' B' ∧
      σ' '' B' = U ∩ {x | f x = f a} := by
  let B' := e ⁻¹' B
  let σ' := σ ∘ e
  have he0 : e (0 : V) = 0 := map_zero e
  have hd : HasFDerivAt σ' (D.comp e.toContinuousLinearMap) 0 := by
    exact (he0.symm ▸ hD).comp 0 e.hasFDerivAt
  refine ⟨B', σ', hB.preimage e.continuous, ?_, ?_, ?_, ?_, ?_, hd, ?_, ?_, ?_⟩
  · simpa [B'] using h0
  · exact hσ.comp e.contDiff.contDiffOn (fun _ h ↦ h)
  · simpa [σ'] using hσ0
  · exact hmap.comp (fun _ h ↦ h)
  · intro w hw
    exact hlevel (e w) hw
  · rw [hd.fderiv]
    exact hDi.comp e.injective
  · intro u hu v hv h
    exact e.injective (hi hu hv h)
  · rw [Set.image_comp, e.surjective.image_preimage, himage]

/-- A regular smooth potential on real times V constructs an actual local level chart
parameterized by V, including the full nearby level set and its true immersion. -/
theorem exists_smooth_graphLevelChart {f : (ℝ × V) → ℝ} {Ω : Set (ℝ × V)}
    {a : ℝ × V} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (ha : a ∈ Ω)
    (hp : fderiv ℝ f a ≠ 0) :
    ∃ (B : Set V) (σ : V → ℝ × V) (U : Set (ℝ × V)),
      IsOpen B ∧ (0 : V) ∈ B ∧ IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ σ B ∧ σ 0 = a ∧ MapsTo σ B Ω ∧
      (∀ w ∈ B, f (σ w) = f a) ∧ Function.Injective (fderiv ℝ σ 0) ∧
      InjOn σ B ∧ σ '' B = U ∩ {x | f x = f a} := by
  obtain ⟨B, σ, U, hB, h0, hσ, hσ0, hmap, hlevel, hD, _, hi,
    hU, haU, hUΩ, himage, _⟩ := exists_smooth_levelChart hΩ hf ha hp
  let e := graphCovectorKernelEquiv (fderiv ℝ f a) hp
  obtain ⟨B', σ', hB', h0', hσ', hσ0', hmap', hlevel', _, hDi', hi', himage'⟩ :=
    reparam_levelChart e hB h0 hσ hσ0 hmap hlevel hD Subtype.val_injective hi himage
  exact ⟨B', σ', U, hB', h0', hU, haU, hUΩ, hσ', hσ0', hmap', hlevel',
    hDi', hi', himage'⟩

end OTSelector.Geometry

end
end
