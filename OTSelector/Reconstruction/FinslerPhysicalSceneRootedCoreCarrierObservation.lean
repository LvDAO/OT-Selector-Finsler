import OTSelector.MeasureTheory.IteratedWeakClosedCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylor

/-! The closed-core weak carrier uses the actual original physical observation.
Its shrinking-offset identity follows from the same original source coordinate. -/
open Set Function MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

omit [MeasurableSpace M] in
/-- The same original source coordinate is recovered exactly from its actual
macroscopic tag and microscopic physical source endpoint. -/
theorem physicalSceneRootedObservation_original_coordinate
    {scale : ℝ} (hscale : scale ≠ 0) (coord : M → (ι → ℝ))
    (u : M → ℝ) (root : ι → ℝ) (e : M × M) :
    physicalSceneMacroscopicRoot scale root + scale⁻¹ •
      (physicalSceneRootedObservation (fun x ↦ scale • coord x) u root e).1.1 = coord e.1 := by
  rw [physicalSceneMacroscopicRoot_eq_inv_smul]
  exact (coordinate_eq_macro_add_scaled_rooted_residual scale hscale (coord e.1) root).symm

/-- An actual original source carrier supplies the shrinking-offset hypothesis
of the weak core-carrier theorem after the literal physical observation.
The original clock, root, plan and total-mass factor remain unchanged. -/
theorem ae_physicalSceneRootedPlan_originalCore
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {scale : ℝ} (hscale : scale ≠ 0)
    (N : ℝ) (root : ι → ℝ) {K : Set (ι → ℝ)} (hK : MeasurableSet K)
    (hcarried : ∀ᵐ e ∂Γ, coord e.1 ∈ K) :
    ∀ᵐ e ∂physicalSceneRootedPlan Γ (fun x ↦ scale • coord x) u N root,
      physicalSceneMacroscopicRoot scale root + scale⁻¹ • e.1.1 ∈ K := by
  apply Measure.ae_smul_measure
  have hf := measurable_physicalSceneRootedObservation
    (fun x ↦ scale • coord x) (hcoord.const_smul scale) u hu root
  have hpred : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
      physicalSceneMacroscopicRoot scale root + scale⁻¹ • e.1.1 ∈ K} :=
    hK.preimage (measurable_const.add (measurable_fst.fst.const_smul scale⁻¹))
  apply (ae_map_iff hf.aemeasurable hpred).mpr
  filter_upwards [hcarried] with e he
  rwa [physicalSceneRootedObservation_original_coordinate hscale]

end OTSelector.Reconstruction
