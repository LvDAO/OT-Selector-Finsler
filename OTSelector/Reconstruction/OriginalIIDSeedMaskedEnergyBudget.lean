import OTSelector.Reconstruction.OriginalIIDTranslatedWindowBudget
import OTSelector.Reconstruction.FinslerOriginalAtlasEnergyBudget

/-!
# One original physical budget across seed masks

The finite shifted-window estimate retains its actual source-masked energy.
Countably many disjoint original seed masks share the same sampled optimizer
and spend the original global energy once, even when their coordinate frames
and finite collections of local cells differ.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

/-- All actual translated cells of one fixed original seed consume its own
masked physical energy, with one Taylor error times its original source mass. -/
theorem lintegral_originalIID_translated_window_sum_le_masked
    {I M : Type*} [Fintype I] [MeasurableSpace M] {q : ℕ}
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (selectionScale : ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (Fin q → ℝ)) (hcoord : Measurable coord)
    (physicalEnergy : M × M → ℝ) (he : Measurable physicalEnergy) (ε : ℝ)
    {s : ℝ} (hs : s ≠ 0) (center : I → (Fin q → ℝ))
    (domains : I → Set (Fin q → ℝ)) (hdomains : ∀ i, MeasurableSet (domains i))
    (cells : I → Set (Fin q → ℝ)) (hcells : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j)))
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ∞) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
    let ΓH := fun ξ ↦ (Γ ξ).restrict (H ×ˢ univ)
    (∑ i, ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
      cavityRootWindowReadout (ΓH ξ) (fun p ↦ coord p.1)
        (fun p ↦ ENNReal.ofReal (physicalEnergy p+ε)) U (root+s • center i)
      ∂cavityRootMeasure volume
        (domains i ∩ (fun root ↦ center i+physicalSceneMacroscopicRoot s root) ⁻¹' cells i)
        ((n : ℝ)+1) ∂law) ≤
    volume U * ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂ΓH ξ ∂law) +
      ENNReal.ofReal ε * μ H) := by
  intro law Γ ΓH
  have hΓH : Measurable ΓH := measurable_physicalPlan_sourceRestriction _
    (measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale) H hH
  have hE : Measurable (fun ξ ↦ ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂ΓH ξ) :=
    (Measure.measurable_lintegral he.ennreal_ofReal).comp hΓH
  have hmass : (∫⁻ ξ, ΓH ξ univ ∂law) = μ H := by
    have hp : H ×ˢ (univ : Set M) = Prod.fst ⁻¹' H := by ext p; simp
    simpa only [ΓH,Γ,Measure.restrict_apply_univ,hp] using
      lintegral_originalIIDOptimalPhysicalPlan_source_event μ ν cost selectionScale hH
  have hupper : (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p+ε) ∂ΓH ξ ∂law) ≤
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂ΓH ξ ∂law) +
        ENNReal.ofReal ε * μ H := by
    calc
      _ ≤ ∫⁻ ξ, (∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂ΓH ξ) +
          ENNReal.ofReal ε * ΓH ξ univ ∂law := by
        apply lintegral_mono
        intro ξ
        exact (lintegral_mono (fun p ↦ ENNReal.ofReal_add_le)).trans_eq (by
          rw [lintegral_add_left he.ennreal_ofReal,lintegral_const])
      _ = (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂ΓH ξ ∂law) +
          ENNReal.ofReal ε * μ H := by
        rw [lintegral_add_left hE,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hmass]
  exact (lintegral_expected_original_translated_window_sum_le law ΓH
    (fun p ↦ coord p.1) (hcoord.comp measurable_fst)
    (fun _ p ↦ ENNReal.ofReal (physicalEnergy p+ε))
    (fun _ ↦ (he.add_const ε).ennreal_ofReal) hs center domains hdomains
    cells hcells hdisjoint U hU hUf ((n : ℝ)+1) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hupper bot_le)


section OriginalSeeds
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))

include hF hcomplete hu ha hinj in
/-- The original countable seed source masses consume at most the original
source probability mass. Taylor errors therefore have no seed-count factor. -/
theorem tsum_originalSeed_source_mass_le_one
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (∑' j, μ (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j)) ≤ 1 := by
  rw [← measure_iUnion pairwiseDisjoint_physicalSceneOriginalSeedSource
    (fun j ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)]
  exact prob_le_one

include hF hcomplete hu ha hinj in
/-- Countably many actual original seed restrictions of one iid optimizer
share its single original expected physical energy budget. This is the existing
pointwise partition theorem averaged in the original two-product experiment. -/
theorem tsum_originalIID_seed_masked_energy_le
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (selectionScale : ℝ) (physicalEnergy : M × M → ℝ) (he : Measurable physicalEnergy) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
    let H := fun j ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j
    (∑' j, ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
      ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) ≤
        ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂Γ ξ ∂law := by
  intro law Γ H
  have hE (j : ℕ) : Measurable (fun ξ ↦
      ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂(Γ ξ).restrict (H j ×ˢ univ)) :=
    (Measure.measurable_lintegral he.ennreal_ofReal).comp
      (measurable_physicalPlan_sourceRestriction _
        (measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale) (H j)
        (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j))
  rw [← lintegral_tsum (fun j ↦ (hE j).aemeasurable)]
  apply lintegral_mono
  intro ξ
  exact tsum_originalSeed_sourceEnergy_le hF hcomplete hu ha hinj (Γ ξ)
    (fun p ↦ ENNReal.ofReal (physicalEnergy p))

include hF hcomplete hu ha hinj in
/-- Any finite collection of distinct original seed indices spends at most
that same actual iid physical-energy budget. -/
theorem sum_originalIID_seed_masked_energy_le
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (selectionScale : ℝ) (physicalEnergy : M × M → ℝ) (he : Measurable physicalEnergy)
    (J : Finset ℕ) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
    let H := fun j ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j
    (∑ j ∈ J, ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
      ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) ≤
        ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂Γ ξ ∂law := by
  intro law Γ H
  exact (ENNReal.sum_le_tsum J).trans
    (tsum_originalIID_seed_masked_energy_le hF hcomplete hu ha hinj
      μ ν n cost hcost selectionScale physicalEnergy he)

include hF hcomplete hu ha hinj in
/-- Different seed coordinate spaces and finite cell families may have different
window volumes. Once their true masked estimates are established, a common
volume bound pays their countable sum by one actual global iid energy plus
one Taylor error, without an assumed replacement energy budget. -/
theorem tsum_originalIID_seed_readouts_le_single_budget
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (selectionScale : ℝ) (physicalEnergy : M × M → ℝ) (he : Measurable physicalEnergy)
    (ε : ℝ) (readout windowVolume : ℕ → ℝ≥0∞) (commonVolume : ℝ≥0∞)
    (hvolume : ∀ j, windowVolume j ≤ commonVolume) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
    let H := fun j ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j
    (∀ j, readout j ≤ windowVolume j *
      ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
        ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) + ENNReal.ofReal ε * μ (H j))) →
    (∑' j, readout j) ≤ commonVolume *
      ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂Γ ξ ∂law) + ENNReal.ofReal ε) := by
  intro law Γ H hreadout
  have henergy := tsum_originalIID_seed_masked_energy_le (P := P) (κ := κ) (lambda := lambda)
    hF hcomplete hu ha hinj
    μ ν n cost hcost selectionScale physicalEnergy he
  have hmass := tsum_originalSeed_source_mass_le_one (P := P) (κ := κ) (lambda := lambda)
    hF hcomplete hu ha hinj μ
  calc
    _ ≤ ∑' j, commonVolume *
        ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
          ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) + ENNReal.ofReal ε * μ (H j)) :=
      ENNReal.tsum_le_tsum (fun j ↦ (hreadout j).trans
        (mul_le_mul_of_nonneg_right (hvolume j) bot_le))
    _ = commonVolume * ((∑' j, ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
        ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) +
        ENNReal.ofReal ε * ∑' j, μ (H j)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add henergy (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmass (bot_le : 0 ≤ ENNReal.ofReal ε))) bot_le

include hF hcomplete hu ha hinj in
/-- The same common-volume conclusion for a finite set of original seeds
requires local window estimates only on those selected indices. -/
theorem sum_originalIID_seed_readouts_le_single_budget
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (selectionScale : ℝ) (physicalEnergy : M × M → ℝ) (he : Measurable physicalEnergy)
    (ε : ℝ) (J : Finset ℕ) (readout windowVolume : ℕ → ℝ≥0∞)
    (commonVolume : ℝ≥0∞) (hvolume : ∀ j ∈ J, windowVolume j ≤ commonVolume) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
    let H := fun j ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j
    (∀ j ∈ J, readout j ≤ windowVolume j *
      ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
        ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) + ENNReal.ofReal ε * μ (H j))) →
    (∑ j ∈ J, readout j) ≤ commonVolume *
      ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂Γ ξ ∂law) + ENNReal.ofReal ε) := by
  intro law Γ H hreadout
  have henergy := tsum_originalIID_seed_masked_energy_le (P := P) (κ := κ) (lambda := lambda)
    hF hcomplete hu ha hinj
    μ ν n cost hcost selectionScale physicalEnergy he
  have hmass := tsum_originalSeed_source_mass_le_one (P := P) (κ := κ) (lambda := lambda)
    hF hcomplete hu ha hinj μ
  calc
    _ ≤ ∑ j ∈ J, commonVolume *
        ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
          ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) + ENNReal.ofReal ε * μ (H j)) :=
      Finset.sum_le_sum (fun j hj ↦ (hreadout j hj).trans
        (mul_le_mul_of_nonneg_right (hvolume j hj) bot_le))
    _ ≤ ∑' j, commonVolume *
        ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
          ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) + ENNReal.ofReal ε * μ (H j)) :=
      ENNReal.sum_le_tsum J
    _ = commonVolume * ((∑' j, ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p)
        ∂(Γ ξ).restrict (H j ×ˢ univ) ∂law) +
        ENNReal.ofReal ε * ∑' j, μ (H j)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add henergy (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmass (bot_le : 0 ≤ ENNReal.ofReal ε))) bot_le

end OriginalSeeds
end OTSelector.Reconstruction
