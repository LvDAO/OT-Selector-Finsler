import OTSelector.Reconstruction.FinslerPhysicalSceneRootGrid

/-!
# Finite original root laws recover the whole compact macro probe

Compact macroscopic support chooses finitely many literal unit root boxes
before the original sample or scale is chosen. Their sum is the full Haar
readout of the unchanged plan, with both original clocks retained.
-/
open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability BoxIntegral
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]
local notation "V" => (ι → ℝ)
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))

/-- A compact macroscopic clock probe uses finitely many original root boxes.
The collection is fixed before all sample sizes, plans and source cutoffs. -/
theorem exists_finite_macro_clockProbe_root_recovery
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    ∃ cells : Finset (ι → ℤ), ∀ (scale N : ℝ) (π : V → Measure Edge)
      (η : V → ℝ≥0∞),
    (∑ ν ∈ cells, ∫⁻ z, physicalSceneMacroClockProbe (π z) (scale⁻¹ • z) η
      (fun w ↦ ENNReal.ofReal (g w))
        ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) =
      ∫⁻ z, physicalSceneMacroClockProbe (π z) (scale⁻¹ • z) η
        (fun w ↦ ENNReal.ofReal (g w)) ∂cavityRootMeasure volume univ N := by
  obtain ⟨cells, hcells⟩ := exists_finite_unit_root_grid_cover
    (g.hasCompactSupport.isCompact.image continuous_fst).isBounded
  refine ⟨cells, ?_⟩
  intro scale N π η
  apply sum_lintegral_cavityRoot_grid_eq
  intro z hz
  by_contra hn
  have hnot : scale⁻¹ • z ∉ Prod.fst '' tsupport g := by
    intro h
    have hh := hcells h
    simp only [mem_iUnion] at hh
    obtain ⟨ν, hν, hbox⟩ := hh
    exact hn (mem_biUnion hν hbox)
  have hg0 (st : ℝ × ℝ) : g (scale⁻¹ • z, st) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (mem_image_of_mem Prod.fst h))
  apply hz
  simp only [physicalSceneMacroClockProbe, physicalSceneRootedClockProbe,
    hg0, ENNReal.ofReal_zero, mul_zero, lintegral_zero]

/-- The finite original normalized root laws recover the exact original
same-plan convolution. Their probability normalization follows from the
original scale power, and the finite box set never depends on the sample. -/
theorem exists_finite_original_macroProbe_root_convolution
    {M : Type*} [MeasurableSpace M]
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    ∃ cells : Finset (ι → ℤ), ∀ (Γ : Measure (M × M)) [SFinite Γ]
      (coord : M → V), Measurable coord →
      ∀ (u : M → ℝ), Measurable u →
      ∀ (scale N : ℝ), 0 < scale → 0 < N → scale ^ Fintype.card ι = N →
      ∀ (η : V → ℝ≥0∞), Measurable η →
      (∀ ν : ι → ℤ, IsProbabilityMeasure
        (cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N)) ∧
      (∑ ν ∈ cells, ∫⁻ z, physicalSceneMacroClockProbe
        (physicalSceneRootedPlan Γ coord u N z) (scale⁻¹ • z) η
          (fun w ↦ ENNReal.ofReal (g w))
            ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) =
        ∫⁻ p, ∫⁻ v, η v * ENNReal.ofReal
          (g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2))) ∂volume ∂Γ := by
  obtain ⟨cells, hcells⟩ := exists_finite_macro_clockProbe_root_recovery g
  refine ⟨cells, ?_⟩
  intro Γ _ coord hcoord u hu scale N hscale hN hpower η hη
  constructor
  · intro ν
    apply isProbabilityMeasure_cavityRootMeasure volume _ N hN
    rw [volume_physicalSceneRootGridDomain scale hscale ν, hpower]
  · rw [hcells scale N (fun z ↦ physicalSceneRootedPlan Γ coord u N z) η]
    exact lintegral_physicalSceneMacroClockProbe_eq_convolution Γ coord hcoord u hu N hN
      (fun z ↦ scale⁻¹ • z) (measurable_const_smul _) η hη
      (fun w ↦ ENNReal.ofReal (g w)) g.continuous.measurable.ennreal_ofReal

end OTSelector.Reconstruction
