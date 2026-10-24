import OTSelector.Probability.InvariantConditionalKernel
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootParameter
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootTagged
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Conditional spatial stationarity for actual original physical scenes

The countable rational translation family is dense in the original transverse
space. Actual compact-test parameter continuity extends its conditional
invariance to all physical translations on one full-measure original-root set.
The final producer starts from the original two plans and their retained
macroscopic Haar root rather than an assumed stationary conditional law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

local instance markedStationaryValueHaarRootConditionalPhysicalLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

local instance markedStationaryValueHaarRootConditionalPhysicalLocalInst2 : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- The actual joint-root conditional kernels are invariant under every
physical reroot on one common full-measure set of retained original roots. -/
theorem ae_forall_measurePreserving_physicalSceneReroot_condKernel
    {T : Type*} [MeasurableSpace T]
    (ρ : Measure (T × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) [IsFiniteMeasure ρ]
    (hjoint : ∀ v : ι → ℝ, MeasurePreserving (Prod.map id (physicalSceneReroot v)) ρ ρ) :
    ∀ᵐ w ∂ρ.fst, ∀ v : ι → ℝ,
      MeasurePreserving (physicalSceneReroot v) (ρ.condKernel w) (ρ.condKernel w) := by
  have hdense : DenseRange (fun r : ι → ℚ ↦ (fun i ↦ (r i : ℝ))) := by
    exact DenseRange.piMap (fun _ ↦ Rat.denseRange_cast)
  exact ae_forall_measurePreserving_condKernel_of_joint_dense ρ physicalSceneReroot
    (fun v ↦ (continuous_physicalSceneReroot v).measurable)
    continuous_physicalSceneReroot_parameter _ hdense (fun r ↦ hjoint (fun i ↦ (r i : ℝ)))

/-- Actual original physical plans, the original macroscopic root z/scale,
and a weak limit supply conditional spatial stationarity internally. No
conditional-stationarity premise or replacement scene law is used. -/
theorem ae_conditional_physicalSceneReroot_of_macroRooted_tendsto
    {M : Type*} [MeasurableSpace M]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Γplus Γminus : ∀ n, Ω n → Measure (M × M))
    [∀ n w, IsFiniteMeasure (Γplus n w)] [∀ n w, IsFiniteMeasure (Γminus n w)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (N R scale : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hlarge : Tendsto R atTop atTop) (hscale : Tendsto scale atTop atTop)
    (μ : ℕ → ProbabilityMeasure
      ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {ν : ProbabilityMeasure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hlaw : ∀ n, (μ n : Measure _) = haarCubeAverageLaw (P n)
      (fun p ↦ ((fun i ↦ p.2 i / scale n), physicalSceneRootedLocalScene
        (Γplus n) (Γminus n) (coord n) u (N n) p)) (R n))
    (hlim : Tendsto μ atTop (𝓝 ν)) :
    ∀ᵐ w ∂(ν : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).fst, ∀ v : ι → ℝ,
      MeasurePreserving (physicalSceneReroot v)
        ((ν : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w) ((ν : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w) := by
  apply ae_forall_measurePreserving_physicalSceneReroot_condKernel (ν : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
  intro v
  exact measurePreserving_macroRoot_of_haarCubeAverageLaw_tendsto P
    (fun n ↦ physicalSceneRootedLocalScene (Γplus n) (Γminus n) (coord n) u (N n))
    (fun n ↦ measurable_physicalSceneRootedLocalScene _ _ (hplus n) (hminus n)
      (coord n) (hcoord n) u hu (N n)) R scale hR hlarge hscale μ hlaw hlim
    (continuous_physicalSceneReroot v) v (fun n w z ↦
      physicalSceneReroot_localScene v (Γplus n) (Γminus n) (coord n) (hcoord n) u hu (N n) w z)

end OTSelector.Reconstruction
