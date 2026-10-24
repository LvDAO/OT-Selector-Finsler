import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTightness

/-! All countably many root frames of the same original two-color iid optimal
plans admit one common sample subsequence. Tightness follows from their actual
probability mass, and no independent per-frame extraction is substituted. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {M : Type*} [MeasurableSpace M]
local instance originalIIDCommonRootedPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The same original iid plans admit a common subsequence when the actual cost
varies with sample size. This includes a growing slack term plus a fixed tilt,
without changing or replacing the finite optimal assignments. -/
theorem exists_originalIID_common_rooted_subsequence_varying_cost
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (scale : ℕ → ℝ)
    (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (D : ∀ j, ℕ → Set (axes j → ℝ))
    (hD : ∀ j n, volume (D j n) = ENNReal.ofReal (N n)) :
    let P := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (scale n)
    let hΓ := fun n ↦ measurable_originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (hcost n) (scale n)
    let laws := fun j n ↦ physicalSceneRestrictedRootedLocalSceneLaw
      (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (H j) (hH j)
      (coord j n) (hcoord j n) u hu (N n) (hN n) (D j n) (hD j n)
    ∃ Q : ∀ j, ProbabilityMeasure
        (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j)) := by
  intro P Γ hΓ laws
  have hmass (n : ℕ) : (∫⁻ w, Γ n w univ ∂P n) ≤ 1 := by
    simp only [Γ, measure_univ, lintegral_const, P, measure_univ, mul_one, le_refl]
  have htight (j : ℕ) : IsTightMeasureSet
      (range (fun n ↦ (laws j n : Measure
        (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ))))) :=
    isTightMeasureSet_physicalSceneRestrictedRootedLocalSceneLaw P Γ Γ hΓ hΓ
      (fun _ ↦ H j) (fun _ ↦ hH j) (coord j) (hcoord j) u hu N hN (D j) (hD j)
      1 (by simp) hmass hmass
  let K := fun j ↦ closure (range (laws j))
  have hK (j : ℕ) : IsCompact (K j) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight j using 1
    ext ρ
    simp
  have hc : IsCompact (Set.pi univ K) := isCompact_univ_pi hK
  obtain ⟨Q, _, φ, hφ, hlim⟩ := hc.isSeqCompact
    (fun n j _ ↦ subset_closure (mem_range_self n))
  refine ⟨Q, φ, hφ, ?_⟩
  intro j
  exact ((continuous_apply j).tendsto Q).comp hlim

/-- The actual same iid finite optimal plans, restricted in countably many
measurable original source pieces, have jointly compatible weak limits on one
common sample subsequence. All original samples and root laws are preserved.
This compactness assertion does not assert a Poisson or stationary limit law. -/
theorem exists_originalIID_common_rooted_subsequence
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℕ → ℝ)
    (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (D : ∀ j, ℕ → Set (axes j → ℝ))
    (hD : ∀ j n, volume (D j n) = ENNReal.ofReal (N n)) :
    let P := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) cost (scale n)
    let hΓ := fun n ↦ measurable_originalIIDOptimalPhysicalPlan (n := n + 1) cost hcost (scale n)
    let laws := fun j n ↦ physicalSceneRestrictedRootedLocalSceneLaw
      (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (H j) (hH j)
      (coord j n) (hcoord j n) u hu (N n) (hN n) (D j n) (hD j n)
    ∃ Q : ∀ j, ProbabilityMeasure
        (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j)) := by
  exact exists_originalIID_common_rooted_subsequence_varying_cost
    axes μ ν (fun _ ↦ cost) (fun _ ↦ hcost) scale H hH coord hcoord u hu N hN D hD

end OTSelector.Reconstruction
