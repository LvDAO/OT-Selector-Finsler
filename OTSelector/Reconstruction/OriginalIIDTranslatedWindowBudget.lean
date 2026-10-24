import OTSelector.Reconstruction.OriginalIIDActualKineticFinite
import OTSelector.Reconstruction.OriginalIIDFixedCandidateRootRecovery

/-! Translated original frames use one physical window budget. The root
translation is exact, and disjoint original macroscopic cells stay disjoint
in the original scaled coordinates before any energy is averaged. -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The translated original root has the original macroscopic tag. -/
theorem physicalSceneMacroscopicRoot_add_scale_center
    {ι : Type*} [Fintype ι] {s : ℝ} (hs : s ≠ 0) (center root : ι → ℝ) :
    physicalSceneMacroscopicRoot s (s • center + root) =
      center + physicalSceneMacroscopicRoot s root := by
  ext i
  simp [physicalSceneMacroscopicRoot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_div,hs]

/-- Arbitrary translated frame domains restrict to disjoint original cells.
The domain intersections need no boundary-null condition. -/
theorem pairwiseDisjoint_original_translated_root_cells
    {I ι : Type*} [Fintype ι] {s : ℝ} (hs : s ≠ 0)
    (center : I → (ι → ℝ)) (domains cells : I → Set (ι → ℝ))
    (hd : Pairwise (fun i j ↦ Disjoint (cells i) (cells j))) :
    Pairwise (fun i j ↦ Disjoint
      ((fun root ↦ s • center i + root) ''
        (domains i ∩ (fun root ↦ center i + physicalSceneMacroscopicRoot s root) ⁻¹' cells i))
      ((fun root ↦ s • center j + root) ''
        (domains j ∩ (fun root ↦ center j + physicalSceneMacroscopicRoot s root) ⁻¹' cells j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro root ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hx' : physicalSceneMacroscopicRoot s (s • center i + x) ∈ cells i := by
    rw [physicalSceneMacroscopicRoot_add_scale_center hs]
    exact hx.2
  have hy' : physicalSceneMacroscopicRoot s (s • center i + x) ∈ cells j := by
    change s • center j + y = s • center i + x at heq
    rw [← heq,physicalSceneMacroscopicRoot_add_scale_center hs]
    exact hy.2
  exact Set.disjoint_left.mp (hd hij) hx' hy'

/-- All translated frame windows consume the same original sample energy
once, even when each frame uses its own original root domain. -/
theorem lintegral_expected_original_translated_window_sum_le
    {I Ω X ι : Type*} [Fintype I] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace X]
    (η : Measure Ω) (Γ : Ω → Measure X) [∀ ω, IsFiniteMeasure (Γ ω)]
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (upper : Ω → X → ℝ≥0∞) (hupper : ∀ ω, Measurable (upper ω))
    {s : ℝ} (hs : s ≠ 0) (center : I → (ι → ℝ))
    (domains : I → Set (ι → ℝ)) (hdomains : ∀ i, MeasurableSet (domains i))
    (cells : I → Set (ι → ℝ)) (hcells : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j)))
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ∞)
    (N : ℝ) (hN : 0 < N) :
    (∑ i, ∫⁻ ω, ∫⁻ root, ENNReal.ofReal N *
      cavityRootWindowReadout (Γ ω) coord (upper ω) U (root + s • center i)
      ∂cavityRootMeasure volume
        (domains i ∩ (fun root ↦ center i + physicalSceneMacroscopicRoot s root) ⁻¹' cells i) N ∂η) ≤
      volume U * ∫⁻ ω, ∫⁻ x, upper ω x ∂Γ ω ∂η := by
  let shiftedCells := fun i ↦ (fun root ↦ s • center i + root) ''
    (domains i ∩ (fun root ↦ center i + physicalSceneMacroscopicRoot s root) ⁻¹' cells i)
  have hmeas (i : I) : MeasurableSet (shiftedCells i) :=
    (measurableEmbedding_addLeft (s • center i)).measurableSet_image.mpr
      ((hdomains i).inter ((hcells i).preimage
        (measurable_const.add (continuous_physicalSceneMacroscopicRoot s).measurable)))
  have hd := pairwiseDisjoint_original_translated_root_cells hs center domains cells hdisjoint
  have heq (i : I) (ω : Ω) :
      (∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout (Γ ω) coord (upper ω) U
        (root + s • center i) ∂cavityRootMeasure volume
          (domains i ∩ (fun root ↦ center i + physicalSceneMacroscopicRoot s root) ⁻¹' cells i) N) =
      ∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout (Γ ω) coord (upper ω) U root
        ∂cavityRootMeasure volume (univ ∩ shiftedCells i) N := by
    simpa only [shiftedCells,univ_inter,add_comm] using lintegral_cavityRootMeasure_add_const
      (domains i ∩ (fun root ↦ center i + physicalSceneMacroscopicRoot s root) ⁻¹' cells i)
      N (s • center i)
      (fun root ↦ ENNReal.ofReal N * cavityRootWindowReadout (Γ ω) coord (upper ω) U root)
  simp_rw [heq]
  exact lintegral_expected_cavityRoot_disjoint_domains_window_sum_le η Γ coord hcoord
    upper hupper univ U hU hUf N hN shiftedCells hmeas hd

/-- In the actual two-product iid experiment, every translated original
cell shares the SAME optimizer and source mask. The Taylor error is paid as
exact epsilon times the original masked source mass, once for all cells. -/
theorem lintegral_originalIID_translated_window_sum_le
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
    volume U * ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂Γ ξ ∂law) +
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
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy p) ∂Γ ξ ∂law) +
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
      _ ≤ _ := add_le_add (lintegral_mono (fun ξ ↦
        lintegral_mono' Measure.restrict_le_self le_rfl)) le_rfl
  exact (lintegral_expected_original_translated_window_sum_le law ΓH
    (fun p ↦ coord p.1) (hcoord.comp measurable_fst)
    (fun _ p ↦ ENNReal.ofReal (physicalEnergy p+ε))
    (fun _ ↦ (he.add_const ε).ennreal_ofReal) hs center domains hdomains
    cells hcells hdisjoint U hU hUf ((n : ℝ)+1) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hupper bot_le)

end OTSelector.Reconstruction
