import OTSelector.Geometry.Finsler.Energy.Transition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ManifoldPositionRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ManifoldPositionRank`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual differentiable chart transitions with invertible tangent maps and the indicated manifold position family.

Objects: Intrinsic position-kernel and injectivity invariance under chart changes.

Proof detail: Apply the manifold chain rule and cancel the invertible chart-transition differential.

Sources: John M. Lee, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70 (https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Coordinate-independence adapter for actual derivatives; it assumes no Hamiltonian or Finsler structure.
-/

/-!
# Coordinate invariance of the actual position differential

Changing a legal manifold chart composes the actual parameter derivative with the
invertible derivative of the atlas transition. Its kernel and injectivity are therefore
intrinsic. These are position derivatives, with no phase-rank or Finsler assumption.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The true parameter derivative transforms by the true atlas derivative. -/
theorem fderiv_chartPosition_change (old new : M) {γ : W → M} {w : W}
    (hc : ContinuousAt γ w)
    (ho : γ w ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hn : γ w ∈ (extChartAt 𝓘(ℝ, E) new).source)
    (hd : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w) :
    fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w =
      (fderiv ℝ (chartTransition old new) (extChartAt 𝓘(ℝ, E) new (γ w))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w) := by
  have hy : extChartAt 𝓘(ℝ, E) new (γ w) ∈ chartTransitionDomain old new := by
    refine ⟨(extChartAt 𝓘(ℝ, E) new).map_source hn, ?_⟩
    change (extChartAt 𝓘(ℝ, E) new).symm (extChartAt 𝓘(ℝ, E) new (γ w)) ∈
      (extChartAt 𝓘(ℝ, E) old).source
    rwa [(extChartAt 𝓘(ℝ, E) new).left_inv hn]
  have hT := ((contDiffOn_chartTransition old new).contDiffAt
    ((isOpen_chartTransitionDomain old new).mem_nhds hy)).differentiableAt (by simp)
  have heq : extChartAt 𝓘(ℝ, E) old ∘ γ =ᶠ[𝓝 w]
      chartTransition old new ∘ (extChartAt 𝓘(ℝ, E) new ∘ γ) := by
    filter_upwards [hc.preimage_mem_nhds ((isOpen_extChartAt_source new).mem_nhds hn)]
      with u hu
    change extChartAt 𝓘(ℝ, E) old (γ u) =
      extChartAt 𝓘(ℝ, E) old
        ((extChartAt 𝓘(ℝ, E) new).symm (extChartAt 𝓘(ℝ, E) new (γ u)))
    rw [(extChartAt 𝓘(ℝ, E) new).left_inv hu]
  rw [heq.fderiv_eq, fderiv_comp w hT hd]
  rfl

/-- Legal charts have the same zero parameter directions for the same manifold family. -/
theorem chartPosition_fderiv_eq_zero_iff (old new : M) {γ : W → M} {w : W}
    (hc : ContinuousAt γ w)
    (ho : γ w ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hn : γ w ∈ (extChartAt 𝓘(ℝ, E) new).source)
    (hd : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w) (u : W) :
    fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w u = 0 ↔
      fderiv ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w u = 0 := by
  have hy : extChartAt 𝓘(ℝ, E) new (γ w) ∈ chartTransitionDomain old new := by
    refine ⟨(extChartAt 𝓘(ℝ, E) new).map_source hn, ?_⟩
    change (extChartAt 𝓘(ℝ, E) new).symm (extChartAt 𝓘(ℝ, E) new (γ w)) ∈
      (extChartAt 𝓘(ℝ, E) old).source
    rwa [(extChartAt 𝓘(ℝ, E) new).left_inv hn]
  rw [fderiv_chartPosition_change old new hc ho hn hd]
  change fderiv ℝ (chartTransition old new) _ _ = 0 ↔ _
  exact (map_eq_zero_iff _ (fderiv_chartTransition_injective old new hy))

/-- Position rank is invariant under any legal change of the manifold chart. -/
theorem chartPosition_fderiv_injective_iff (old new : M) {γ : W → M} {w : W}
    (hc : ContinuousAt γ w)
    (ho : γ w ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hn : γ w ∈ (extChartAt 𝓘(ℝ, E) new).source)
    (hd : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w) :
    Function.Injective (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w) ↔
      Function.Injective (fderiv ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w) := by
  have hk : (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w).ker =
      (fderiv ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w).ker := by
    ext u
    exact chartPosition_fderiv_eq_zero_iff old new hc ho hn hd u
  exact (LinearMap.ker_eq_bot (f :=
    (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w).toLinearMap)).symm.trans
      ((show (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w).ker = ⊥ ↔
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) new ∘ γ) w).ker = ⊥ by rw [hk]).trans
        LinearMap.ker_eq_bot)

/-- Having an injective position parameter differential is a property of the manifold
family: it is required in every chart that contains the actual point. -/
def HasInjectiveManifoldPosition (γ : W → M) (w : W) : Prop :=
  ∀ old : M, γ w ∈ (extChartAt 𝓘(ℝ, E) old).source →
    Function.Injective (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w)

/-- One legal differentiable chart suffices to check the intrinsic position rank. -/
theorem hasInjectiveManifoldPosition_iff (old : M) {γ : W → M} {w : W}
    (hc : ContinuousAt γ w) (ho : γ w ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hd : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w) :
    HasInjectiveManifoldPosition (E := E) γ w ↔
      Function.Injective (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w) := by
  refine ⟨fun h ↦ h old ho, ?_⟩
  intro h new hn
  exact (chartPosition_fderiv_injective_iff new old hc hn ho hd).mpr h

/-- The intrinsic position-rank test can be applied directly to a differentiable
manifold parameter family, without supplying its coordinate derivative separately. -/
theorem hasInjectiveManifoldPosition_iff_of_contMDiffAt (old : M) {γ : W → M} {w : W}
    (hγ : ContMDiffAt 𝓘(ℝ, W) 𝓘(ℝ, E) 1 γ w)
    (ho : γ w ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    HasInjectiveManifoldPosition (E := E) γ w ↔
      Function.Injective (fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ γ) w) := by
  have hch : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (extChartAt 𝓘(ℝ, E) old) (γ w) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using ho)
  exact hasInjectiveManifoldPosition_iff old hγ.continuousAt ho
    ((hch.comp w hγ).contDiffAt.differentiableAt (by simp))

end OTSelector.Geometry

end
end
