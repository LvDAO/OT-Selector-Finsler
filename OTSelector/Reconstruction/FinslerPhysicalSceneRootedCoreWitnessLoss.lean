import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearMass
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedAveragePacking

/-!
# Actual average cycle witnesses and original endpoint core loss

Restricting the same original global plans to retained physical endpoint sets
changes each bounded source-window cycle witness only by its actual discarded
mass. Original source and mean target identities pay this mass without changing
any realized restricted columns or the actual root scene.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- A common discarded mass controls the increase of a capped two-rectangle
witness without subtracting possibly infinite masses. -/
theorem physicalScene_capped_min_le_of_common_loss
    (a b a' b' e : ℝ≥0∞) (ha : a ≤ a' + e) (hb : b ≤ b' + e) :
    min 1 (min a b) ≤ min 1 (min a' b') + e := by
  have hm : min a b ≤ min a' b' + e := by
    simpa only [min_add_add_right] using min_le_min ha hb
  calc
    min 1 (min a b) ≤ min 1 (min a' b' + e) := min_le_min_left _ hm
    _ ≤ min (1 + e) (min a' b' + e) :=
      min_le_min_right _ (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ e))
    _ = min 1 (min a' b') + e := min_add_add_right _ _ _

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

/-- The actual rooted observation preserves addition of the original plans. -/
theorem physicalSceneRootedPlan_add
    (Γ₀ Γ₁ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    physicalSceneRootedPlan (Γ₀ + Γ₁) coord u N z =
      physicalSceneRootedPlan Γ₀ coord u N z + physicalSceneRootedPlan Γ₁ coord u N z := by
  simp only [physicalSceneRootedPlan, Measure.map_add _ _
    (measurable_physicalSceneRootedObservation coord hcoord u hu z), smul_add]

/-- Retained and discarded actual endpoint pieces partition the same original
source restriction before and after the rooted observation. -/
theorem physicalSceneRootedPlan_endpoint_core_split
    (Γ : Measure (M × M)) (H : Set M) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z =
      physicalSceneRootedPlan (Γ.restrict (E ∩ (H ×ˢ univ))) coord u N z +
      physicalSceneRootedPlan (Γ.restrict (Eᶜ ∩ (H ×ˢ univ))) coord u N z := by
  have hsplit := Measure.restrict_add_restrict_compl (μ := Γ.restrict (H ×ˢ univ)) hE
  rw [Measure.restrict_restrict hE, Measure.restrict_restrict hE.compl] at hsplit
  rw [← physicalSceneRootedPlan_add _ _ coord hcoord u hu N z, hsplit]

/-- The true arithmetic mean of both actual plans loses only the common
actual discarded source-window mass in its capped rectangle witness. -/
theorem physicalSceneRootedPlan_average_witness_le_core_and_loss
    (Γp Γm : Measure (M × M)) (H : Set M) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (T₀ T₁ W : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hT₀ : T₀ ⊆ W) (hT₁ : T₁ ⊆ W) :
    let avg := fun S ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan (Γp.restrict S) coord u N z +
        physicalSceneRootedPlan (Γm.restrict S) coord u N z)
    min 1 (min (avg (H ×ˢ univ) T₀) (avg (H ×ˢ univ) T₁)) ≤
      min 1 (min (avg (E ∩ (H ×ˢ univ)) T₀) (avg (E ∩ (H ×ˢ univ)) T₁)) +
        avg (Eᶜ ∩ (H ×ˢ univ)) W := by
  let avg := fun S ↦ (2 : ℝ≥0∞)⁻¹ •
    (physicalSceneRootedPlan (Γp.restrict S) coord u N z +
      physicalSceneRootedPlan (Γm.restrict S) coord u N z)
  have hsplit : avg (H ×ˢ univ) = avg (E ∩ (H ×ˢ univ)) + avg (Eᶜ ∩ (H ×ˢ univ)) := by
    dsimp only [avg]
    rw [physicalSceneRootedPlan_endpoint_core_split Γp H E hE coord hcoord u hu N z,
      physicalSceneRootedPlan_endpoint_core_split Γm H E hE coord hcoord u hu N z]
    simp only [smul_add, add_assoc, add_left_comm, add_comm]
  change min 1 (min (avg (H ×ˢ univ) T₀) (avg (H ×ˢ univ) T₁)) ≤
    min 1 (min (avg (E ∩ (H ×ˢ univ)) T₀) (avg (E ∩ (H ×ˢ univ)) T₁)) +
      avg (Eᶜ ∩ (H ×ˢ univ)) W
  apply physicalScene_capped_min_le_of_common_loss
  · rw [hsplit, Measure.add_apply]
    exact add_le_add le_rfl (measure_mono hT₀)
  · rw [hsplit, Measure.add_apply]
    exact add_le_add le_rfl (measure_mono hT₁)

end OTSelector.Reconstruction
