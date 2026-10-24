import OTSelector.Reconstruction.OriginalIIDCommonRootedSubsequence
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootPhysicalScene

/-! A single common original iid subsequence supplies spatially stationary
pair-scene limits in all countably many original source frames. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {M : Type*} [MeasurableSpace M]
local instance originalIIDCommonStationaryPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The same original iid plans admit a common subsequence when the actual cost
varies with sample size. This includes a growing slack term plus a fixed tilt,
without changing or replacing the finite optimal assignments. -/
theorem exists_originalIID_common_stationary_cube_subsequence_varying_cost
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)] (hq : ∀ j, 0 < Fintype.card (axes j))
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (scale : ℕ → ℝ)
    (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (hlarge : Tendsto N atTop atTop) :
    let P := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (scale n)
    let hΓ := fun n ↦ measurable_originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (hcost n) (scale n)
    let D := fun j n ↦ haarRootCube (axes j) (haarRootRadius (Fintype.card (axes j)) (N n))
    let hD := fun j n ↦ volume_haarRootCube_radius (axes j) (hq j) (hN n)
    let laws := fun j n ↦ physicalSceneRestrictedRootedLocalSceneLaw
      (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (H j) (hH j)
      (coord j n) (hcoord j n) u hu (N n) (hN n) (D j n) (hD j n)
    ∃ Q : ∀ j, ProbabilityMeasure
        (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j))) ∧
        ∀ j (v : axes j → ℝ), MeasurePreserving (physicalSceneReroot v)
          (Q j : Measure _) (Q j : Measure _) := by
  intro P Γ hΓ D hD laws
  obtain ⟨Q, φ, hφ, hweak⟩ := exists_originalIID_common_rooted_subsequence_varying_cost
    axes μ ν cost hcost scale H hH coord hcoord u hu N hN D hD
  refine ⟨Q, φ, hφ, hweak, ?_⟩
  intro j v
  let Γr := fun n w ↦ (Γ n w).restrict (H j ×ˢ (univ : Set M))
  have hr (n : ℕ) : Measurable (Γr n) :=
    measurable_physicalPlan_sourceRestriction (Γ n) (hΓ n) (H j) (hH j)
  have hw : Tendsto (fun n ↦ physicalSceneRootedLocalSceneLaw (P (φ n))
      (Γr (φ n)) (Γr (φ n)) (hr (φ n)) (hr (φ n))
      (coord j (φ n)) (hcoord j (φ n)) u hu (N (φ n)) (hN (φ n))
      (D j (φ n)) (hD j (φ n))) atTop (𝓝 (Q j)) := by
    simpa only [physicalSceneRestrictedRootedLocalSceneLaw] using hweak j
  exact measurePreserving_physicalSceneReroot_of_cubeRooted_tendsto
    (fun n ↦ P (φ n)) (fun n ↦ Γr (φ n)) (fun n ↦ Γr (φ n))
    (fun n ↦ hr (φ n)) (fun n ↦ hr (φ n))
    (fun n ↦ coord j (φ n)) (fun n ↦ hcoord j (φ n)) u hu
    (fun n ↦ N (φ n)) (fun n ↦ haarRootRadius (Fintype.card (axes j)) (N (φ n)))
    (fun n ↦ hN (φ n)) (fun n ↦ haarRootRadius_pos _ (hN (φ n)))
    (fun n ↦ hD j (φ n))
    ((tendsto_haarRootRadius _ (hq j) hlarge).comp hφ.tendsto_atTop) hw v

/-- Actual probability mass produces the simultaneous weak subsequence, and
the original Haar-root cocycle produces its stationarity in each frame. The
same original finite iid plans are retained throughout the construction. -/
theorem exists_originalIID_common_stationary_cube_subsequence
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)] (hq : ∀ j, 0 < Fintype.card (axes j))
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℕ → ℝ)
    (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (hlarge : Tendsto N atTop atTop) :
    let P := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) cost (scale n)
    let hΓ := fun n ↦ measurable_originalIIDOptimalPhysicalPlan (n := n + 1) cost hcost (scale n)
    let D := fun j n ↦ haarRootCube (axes j) (haarRootRadius (Fintype.card (axes j)) (N n))
    let hD := fun j n ↦ volume_haarRootCube_radius (axes j) (hq j) (hN n)
    let laws := fun j n ↦ physicalSceneRestrictedRootedLocalSceneLaw
      (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (H j) (hH j)
      (coord j n) (hcoord j n) u hu (N n) (hN n) (D j n) (hD j n)
    ∃ Q : ∀ j, ProbabilityMeasure
        (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j))) ∧
        ∀ j (v : axes j → ℝ), MeasurePreserving (physicalSceneReroot v)
          (Q j : Measure _) (Q j : Measure _) := by
  exact exists_originalIID_common_stationary_cube_subsequence_varying_cost
    axes hq μ ν (fun _ ↦ cost) (fun _ ↦ hcost) scale H hH coord hcoord u hu N hN hlarge

end OTSelector.Reconstruction
