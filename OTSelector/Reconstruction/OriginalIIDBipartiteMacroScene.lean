import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicHaarMarginal
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale

/-! Both complete original iid input clouds, their actual optimal physical
plan and the macroscopic root are retained in one common original experiment.
Tightness uses their actual mass and a fixed compact macroscopic root cube. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance iidBipartiteMacroStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance iidBipartiteMacroConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance iidBipartiteMacroConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance iidBipartiteMacroConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance iidBipartiteMacroPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "Macro" => (ι → ℝ) ×
  (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)

/-- The same original sample and root retain both full input arrays. The
macro tag and pair plan are shared exactly between the two observations. -/
def originalIIDBipartiteMacroObservation (cost : M → M → ℝ) (k : ℝ) (n : ℕ)
    (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) : Macro × Macro :=
  let Γ := fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ)
  (physicalSceneRootedMacroscopicObservation base Γ Γ coord u ((n : ℝ) + 1) scale
      (fun ξ ↦ ξ.1) w,
    physicalSceneRootedMacroscopicObservation base Γ Γ coord u ((n : ℝ) + 1) scale
      (fun ξ ↦ ξ.2) w)

/-- Joint measurability keeps all optimizer/input correlations of the actual
original experiment, without a product or independence replacement. -/
theorem measurable_originalIIDBipartiteMacroObservation
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k : ℝ) (n : ℕ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ) :
    Measurable (originalIIDBipartiteMacroObservation base cost k n H coord u scale) := by
  let Γ := originalIIDOptimalPhysicalPlan (n := n + 1) cost k
  let Γr := fun ξ ↦ (Γ ξ).restrict (H ×ˢ univ)
  have hr : Measurable Γr := measurable_physicalPlan_sourceRestriction Γ
    (measurable_originalIIDOptimalPhysicalPlan cost hcost k) H hH
  exact (measurable_physicalSceneRootedMacroscopicObservation base Γr Γr hr hr
    coord hcoord u hu ((n : ℝ) + 1) scale (fun ξ ↦ ξ.1)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)).prodMk
      (measurable_physicalSceneRootedMacroscopicObservation base Γr Γr hr hr
        coord hcoord u hu ((n : ℝ) + 1) scale (fun ξ ↦ ξ.2)
        (fun j ↦ (measurable_pi_apply j).comp measurable_snd))

/-- The actual joint original iid/root law uses the mass-n cube and its
corresponding spatial scale; its macroscopic tag stays in the centered unit cube. -/
def originalIIDBipartiteMacroLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k : ℝ) (n : ℕ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) : ProbabilityMeasure (Macro × Macro) := by
  let R := haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let D := haarRootCube ι R
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hD : volume D = ENNReal.ofReal ((n : ℝ) + 1) := volume_haarRootCube_radius ι hq hN
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  exact ⟨(P.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (originalIIDBipartiteMacroObservation base cost k n H coord u (2 * R)),
    Measure.isProbabilityMeasure_map
      (measurable_originalIIDBipartiteMacroObservation base cost hcost k n H hH
        coord hcoord u hu (2 * R)).aemeasurable⟩

/-- Tightness retains the actual optimal physical plan for a measurable cost that may
vary with sample size. The two full input arrays still share their original sample and root. -/
theorem isTightMeasureSet_originalIIDBipartiteMacroLaw_varying_cost
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ)
    (hcost : ∀ n, Measurable (Function.uncurry (cost n))) (k : ℕ → ℝ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) :
    IsTightMeasureSet (range (fun n ↦
      (originalIIDBipartiteMacroLaw base μ ν hq (cost n) (hcost n) (k n) n H hH
        (coord n) (hcoord n) u hu : Measure (Macro × Macro)))) := by
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (k n)
  let Γr := fun n ξ ↦ (Γ n ξ).restrict (H ×ˢ univ)
  have hΓ (n : ℕ) : Measurable (Γ n) := measurable_originalIIDOptimalPhysicalPlan (cost n) (hcost n) (k n)
  have hr (n : ℕ) : Measurable (Γr n) :=
    measurable_physicalPlan_sourceRestriction (Γ n) (hΓ n) H hH
  let R := fun n : ℕ ↦ haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let D := fun n ↦ haarRootCube ι (R n)
  have hR (n : ℕ) : 0 < R n := haarRootRadius_pos _ (by positivity)
  have hD (n : ℕ) : volume (D n) = ENNReal.ofReal ((n : ℝ) + 1) :=
    volume_haarRootCube_radius ι hq (by positivity)
  let P := fun n ↦ (Penv n).prod (cavityRootMeasure volume (D n) ((n : ℝ) + 1))
  have hmass (n : ℕ) : (∫⁻ ξ, Γ n ξ univ ∂Penv n) ≤ 1 := by simp [Γ, Penv]
  have hDK (n : ℕ) (z : ι → ℝ) (hz : z ∈ D n) :
      physicalSceneMacroscopicRoot (2 * R n) z ∈ haarRootCube ι (1 / 2) := by
    have hs : 0 < 2 * R n := mul_pos (by norm_num) (hR n)
    have heq := physicalSceneMacroscopicRoot_preimage_centered_unitCube (ι := ι) hs
    have hd : haarRootCube ι ((2 * R n) / 2) = D n := by dsimp only [D]; congr 1; ring
    rw [hd] at heq
    change z ∈ physicalSceneMacroscopicRoot (2 * R n) ⁻¹' haarRootCube ι (1 / 2)
    rw [heq]
    exact hz
  have htight (Y : ∀ n, ((Fin (n + 1) → M) × (Fin (n + 1) → M)) → Fin (n + 1) → M)
      (hY : ∀ n j, Measurable (fun ξ ↦ Y n ξ j)) :
      IsTightMeasureSet (range (fun n ↦ (P n).map
        (physicalSceneRootedMacroscopicObservation base (Γr n) (Γr n) (coord n) u
          ((n : ℝ) + 1) (2 * R n) (Y n)))) := by
    exact isTightMeasureSet_physicalSceneRootedMacroscopicSceneLaw base id Penv Γ Γ hΓ hΓ
      (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu (fun n ↦ 2 * R n) Y hY D hD
      (haarRootCube ι (1 / 2)) isCompact_Icc hDK 1 (by simp) hmass hmass
  exact isTightMeasureSet_original_joint_of_marginals P
    (fun n ↦ physicalSceneRootedMacroscopicObservation base (Γr n) (Γr n) (coord n) u
      ((n : ℝ) + 1) (2 * R n) (fun ξ ↦ ξ.1))
    (fun n ↦ physicalSceneRootedMacroscopicObservation base (Γr n) (Γr n) (coord n) u
      ((n : ℝ) + 1) (2 * R n) (fun ξ ↦ ξ.2))
    (fun n ↦ measurable_physicalSceneRootedMacroscopicObservation base (Γr n) (Γr n)
      (hr n) (hr n) (coord n) (hcoord n) u hu ((n : ℝ) + 1) (2 * R n)
      (fun ξ ↦ ξ.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    (fun n ↦ measurable_physicalSceneRootedMacroscopicObservation base (Γr n) (Γr n)
      (hr n) (hr n) (coord n) (hcoord n) u hu ((n : ℝ) + 1) (2 * R n)
      (fun ξ ↦ ξ.2) (fun j ↦ (measurable_pi_apply j).comp measurable_snd))
    (htight (fun _ ξ ↦ ξ.1) (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst))
    (htight (fun _ ξ ↦ ξ.2) (fun _ j ↦ (measurable_pi_apply j).comp measurable_snd))

/-- Tightness of the actual joint original two-input/macro scene follows from
the true unit physical mass and the compact original macro cube. No tightness,
input process or limiting-scene callback is supplied. -/
theorem isTightMeasureSet_originalIIDBipartiteMacroLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k : ℕ → ℝ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) :
    IsTightMeasureSet (range (fun n ↦
      (originalIIDBipartiteMacroLaw base μ ν hq cost hcost (k n) n H hH
        (coord n) (hcoord n) u hu : Measure (Macro × Macro)))) := by
  exact isTightMeasureSet_originalIIDBipartiteMacroLaw_varying_cost base μ ν hq
    (fun _ ↦ cost) (fun _ ↦ hcost) k H hH coord hcoord u hu

end OTSelector.Reconstruction
