import OTSelector.Probability.SupportedIID
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanTight
import Mathlib.Topology.TietzeExtension

/-!
# Original supported endpoint probes have ambient continuous readouts

The measurable support projection is used only on its original full-mass
carrier. Tietze extension supplies one ambient bounded continuous probe with
the same exact integrals on every original plan carried by that set.
-/
open Set Function MeasureTheory Topology OTSelector.Probability
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A supported selector probe extends with unchanged norm, and every plan
carried by the original compact population set has exactly its old readout. -/
theorem exists_original_supported_probe_ambient_extension
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K) (f : (K × K) →ᵇ ℝ) :
    ∃ g : (M × M) →ᵇ ℝ, ‖g‖ = ‖f‖ ∧
      (∀ x ∈ K, ∀ y ∈ K, g (x,y) =
        f (supportProjection μ K hK.measurableSet hμ x,
          supportProjection ν K hK.measurableSet hν y)) ∧
      ∀ π : Measure (M × M), (∀ᵐ p ∂π, p ∈ K ×ˢ K) →
        (∫ p, f (supportProjection μ K hK.measurableSet hμ p.1,
          supportProjection ν K hK.measurableSet hν p.2) ∂π) = ∫ p, g p ∂π := by
  have he : IsClosedEmbedding (Prod.map ((↑) : K → M) ((↑) : K → M)) :=
    hK.isClosed.isClosedEmbedding_subtypeVal.prodMap hK.isClosed.isClosedEmbedding_subtypeVal
  obtain ⟨g, hgnorm, hgeq⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding he
  have hpoint (x : M) (hx : x ∈ K) (y : M) (hy : y ∈ K) :
      g (x,y) = f (supportProjection μ K hK.measurableSet hμ x,
        supportProjection ν K hK.measurableSet hν y) := by
    have hh := congrFun hgeq (⟨x,hx⟩, ⟨y,hy⟩)
    have hpμ := supportProjection_coe μ K hK.measurableSet hμ ⟨x,hx⟩
    have hpν := supportProjection_coe ν K hK.measurableSet hν ⟨y,hy⟩
    rw [hpμ, hpν]
    exact hh
  refine ⟨g, hgnorm, hpoint, ?_⟩
  intro π hπ
  apply integral_congr_ae
  filter_upwards [hπ] with p hp
  exact (hpoint p.1 hp.1 p.2 hp.2).symm

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- On the unchanged feasible experiment, one ambient extension reproduces
the supported probe on both original raw global allocation plans almost surely. -/
theorem ae_originalAllocation_supported_probe_eq_ambient
    (R : Measure Ω) (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K) (f : (K × K) →ᵇ ℝ)
    (g : (M × M) →ᵇ ℝ)
    (hg : ∀ π : Measure (M × M), (∀ᵐ p ∂π, p ∈ K ×ˢ K) →
      (∫ p, f (supportProjection μ K hK.measurableSet hμ p.1,
        supportProjection ν K hK.measurableSet hν p.2) ∂π) = ∫ p, g p ∂π)
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (Y : Ω → Fin (n + 1) → M) (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂R, IsSemidiscreteAllocation (μ : Measure M) (p w) (ap w))
    (hfm : ∀ᵐ w ∂R, IsSemidiscreteAllocation (μ : Measure M) (p w) (am w))
    (hY : ∀ᵐ w ∂R, ∀ i, Y w i ∈ K) :
    ∀ᵐ w ∂R,
      (∫ e, f (supportProjection μ K hK.measurableSet hμ e.1,
        supportProjection ν K hK.measurableSet hν e.2)
        ∂physicalSceneGlobalAllocationFamily (μ : Measure M) ap Y w) =
        (∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) ap Y w) ∧
      (∫ e, f (supportProjection μ K hK.measurableSet hμ e.1,
        supportProjection ν K hK.measurableSet hν e.2)
        ∂physicalSceneGlobalAllocationFamily (μ : Measure M) am Y w) =
        (∫ e, g e ∂physicalSceneGlobalAllocationFamily (μ : Measure M) am Y w) := by
  have hp := ae_physicalSceneGlobalAllocationFamily_carried R (μ : Measure M)
    ap Y p hfp hK.measurableSet hK.measurableSet hμ hY
  have hm := ae_physicalSceneGlobalAllocationFamily_carried R (μ : Measure M)
    am Y p hfm hK.measurableSet hK.measurableSet hμ hY
  filter_upwards [hp,hm] with w hpw hmw
  exact ⟨hg _ hpw, hg _ hmw⟩

end OTSelector.Reconstruction
