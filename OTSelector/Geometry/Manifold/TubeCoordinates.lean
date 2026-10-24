import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Geometry.Manifold.TubeCoordinates

## Lemma skeleton

* **Conditions:** An open partial manifold homeomorphism and a continuous linear equivalence from its parameter model to the fixed chart model; regularity is supplied only in the relevant derivative/smoothness declarations.

* **Objects:** A genuine model-space tube chart with explicit source/target, inverse and derivative.

* **Proof detail:** Compose the linear equivalence, original tube and actual manifold chart. Compute legal domains from open-partial-homeomorphism composition. Differentiate the linear change of variables and transfer manifold regularity to chart-coordinate regularity.

## Mathematical sources

- [John M. Lee, Introduction to Smooth Manifolds, second edition (2013)](https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10): Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation (adapter): Coordinate composition retaining the actual linear normalization; no isometric or volume normalization is claimed.
-/

/-!
# Actual manifold tubes expressed in one model space

A continuous linear equivalence identifies the tube parameter space with the
manifold model space. Composing the actual tube and an actual manifold chart gives
an open partial homeomorphism on that model space, with its precise legal domain.
Its ordinary regularity follows from that of the given tube and inverse. The
actual derivative retains the chosen linear normalization; no isometry or volume
normalization is assumed.
-/

open Set Manifold
open scoped ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual tube in an actual chart, with both ends in the same model space. -/
def manifoldTubeChart (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) : OpenPartialHomeomorph E E :=
  (ℓ.symm.toHomeomorph.transOpenPartialHomeomorph Y).trans (chartAt E old)

/-- The coordinate map is the genuine chart, tube, and inverse linear normalization. -/
theorem manifoldTubeChart_coe (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) : (manifoldTubeChart Y ℓ old : E → E) = (chartAt E old) ∘ Y ∘ ℓ.symm := rfl

/-- Its inverse uses the genuine inverse chart and inverse tube. -/
theorem manifoldTubeChart_symm_coe (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) : (manifoldTubeChart Y ℓ old).symm =
      (ℓ : V → E) ∘ Y.symm ∘ (chartAt E old).symm := rfl

/-- The source includes precisely the points where both actual maps are legal. -/
theorem manifoldTubeChart_source (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) : (manifoldTubeChart Y ℓ old).source =
      ℓ.symm ⁻¹' (Y.source ∩ Y ⁻¹' (chartAt E old).source) := rfl

/-- The target is the chart image of the overlap with the actual tube target. -/
theorem manifoldTubeChart_target (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) : (manifoldTubeChart Y ℓ old).target =
      (chartAt E old) '' ((chartAt E old).source ∩ Y.target) :=
  OpenPartialHomeomorph.trans_target'' _ _

/-- Membership in the source records both legal-domain conditions. -/
@[simp] theorem mem_manifoldTubeChart_source_iff (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M) (x : E) :
    x ∈ (manifoldTubeChart Y ℓ old).source ↔
      ℓ.symm x ∈ Y.source ∧ Y (ℓ.symm x) ∈ (chartAt E old).source := Iff.rfl

/-- Membership in the target records the inverse chart and inverse tube domains. -/
@[simp] theorem mem_manifoldTubeChart_target_iff (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M) (x : E) :
    x ∈ (manifoldTubeChart Y ℓ old).target ↔
      x ∈ (chartAt E old).target ∧ (chartAt E old).symm x ∈ Y.target := Iff.rfl

/-- Original tube parameters are legal exactly on the chart overlap. -/
@[simp] theorem apply_mem_manifoldTubeChart_source_iff (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M) (q : V) :
    ℓ q ∈ (manifoldTubeChart Y ℓ old).source ↔
      q ∈ Y.source ∧ Y q ∈ (chartAt E old).source := by simp

/-- The actual derivative keeps the linear normalization explicitly, also at points
where the unrestricted charted tube is not differentiable. -/
theorem fderiv_manifoldTubeChart (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) (q : V) :
    fderiv ℝ (manifoldTubeChart Y ℓ old) (ℓ q) =
      (fderiv ℝ ((chartAt E old) ∘ Y) q).comp ℓ.symm.toContinuousLinearMap := by
  change fderiv ℝ (((chartAt E old) ∘ Y) ∘ ℓ.symm) (ℓ q) = _
  rw [ℓ.symm.comp_right_fderiv]
  simp only [ℓ.symm_apply_apply]

variable {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M]

/-- Manifold regularity of the actual tube gives ordinary regularity on the exact
source of its normalized chart expression. -/
theorem contDiffOn_manifoldTubeChart (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n Y Y.source) :
    ContDiffOn ℝ n (manifoldTubeChart Y ℓ old) (manifoldTubeChart Y ℓ old).source := by
  intro x hx
  change ℓ.symm x ∈ Y.source ∧ Y (ℓ.symm x) ∈ (chartAt E old).source at hx
  have hy := hY.contMDiffAt (Y.open_source.mem_nhds hx.1)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (chartAt E old) (Y (ℓ.symm x)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas old) hx.2
  exact ((hc.comp _ hy).comp _ ℓ.symm.contDiff.contMDiff.contMDiffAt).contDiffAt.contDiffWithinAt

/-- Manifold regularity of the actual inverse gives ordinary regularity on the exact
coordinate target. -/
theorem contDiffOn_manifoldTubeChart_symm (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) n Y.symm Y.target) :
    ContDiffOn ℝ n (manifoldTubeChart Y ℓ old).symm
      (manifoldTubeChart Y ℓ old).target := by
  intro x hx
  change x ∈ (chartAt E old).target ∧ (chartAt E old).symm x ∈ Y.target at hx
  have hy := hi.contMDiffAt (Y.open_target.mem_nhds hx.2)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (chartAt E old).symm x :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas old) hx.1
  exact (ℓ.contDiff.contMDiff.contMDiffAt.comp _ (hy.comp _ hc)).contDiffAt.contDiffWithinAt

end OTSelector.Geometry
