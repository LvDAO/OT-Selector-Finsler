import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock

/-! The original finite iid physical plan becomes literal unit-counted edges
under its true sample-size rooting. Its two counted input marginals are exactly
the unchanged original source and target observations. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {M ι : Type*} [MeasurableSpace M] {n : ℕ}

/-- The actual sample-size prefactor cancels the empirical normalization.
Every original matched edge has unit mass; no selected edges are Poissonized. -/
theorem originalIIDOptimalPhysicalPlan_rooted_eq_counted_edges [NeZero n]
    (cost : M → M → ℝ) (scale : ℝ)
    (ξ : (Fin n → M) × (Fin n → M))
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ) :
    physicalSceneRootedPlan (originalIIDOptimalPhysicalPlan cost scale ξ)
      coord u (n : ℝ) z =
      ∑ i, Measure.dirac (physicalSceneRootedObservation coord u z
        (ξ.1 i, ξ.2 (firstOptimalAssignment
          (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) i))) := by
  rw [physicalSceneRootedPlan, originalIIDOptimalPhysicalPlan, empiricalMeasure,
    Measure.map_smul,
    Measure.map_finset_sum' (measurable_physicalSceneRootedObservation coord hcoord u hu z).aemeasurable]
  simp_rw [Measure.map_dirac' (measurable_physicalSceneRootedObservation coord hcoord u hu z)]
  rw [smul_smul, ENNReal.ofReal_natCast, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n), one_smul]

/-- The rooted source input is the actual unit-counted first iid cloud. -/
theorem originalIIDOptimalPhysicalPlan_rooted_source_counts [NeZero n]
    (cost : M → M → ℝ) (scale : ℝ)
    (ξ : (Fin n → M) × (Fin n → M))
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ) :
    (physicalSceneRootedPlan (originalIIDOptimalPhysicalPlan cost scale ξ)
      coord u (n : ℝ) z).map Prod.fst =
      ∑ i, Measure.dirac (coord (ξ.1 i) - z, u (ξ.1 i)) := by
  rw [originalIIDOptimalPhysicalPlan_rooted_eq_counted_edges cost scale ξ coord hcoord u hu z,
    Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp only [Measure.map_dirac' measurable_fst, physicalSceneRootedObservation]

/-- The rooted target input is the actual unit-counted second iid cloud;
reindexing by the complete optimal permutation preserves every observation. -/
theorem originalIIDOptimalPhysicalPlan_rooted_target_counts [NeZero n]
    (cost : M → M → ℝ) (scale : ℝ)
    (ξ : (Fin n → M) × (Fin n → M))
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ) :
    (physicalSceneRootedPlan (originalIIDOptimalPhysicalPlan cost scale ξ)
      coord u (n : ℝ) z).map Prod.snd =
      ∑ i, Measure.dirac (coord (ξ.2 i) - z, u (ξ.2 i)) := by
  rw [originalIIDOptimalPhysicalPlan_rooted_eq_counted_edges cost scale ξ coord hcoord u hu z,
    Measure.map_finset_sum' measurable_snd.aemeasurable]
  simp only [Measure.map_dirac' measurable_snd, physicalSceneRootedObservation]
  exact Equiv.sum_comp (firstOptimalAssignment
    (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)))
    (fun i ↦ Measure.dirac (coord (ξ.2 i) - z, u (ξ.2 i)))

end OTSelector.Reconstruction
