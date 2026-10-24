import OTSelector.Reconstruction.OriginalIIDUnitDensityValueReadout
import OTSelector.Reconstruction.OriginalIIDActualKineticIntegrability
import OTSelector.Reconstruction.FinslerPopulationHaarCellLaws
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Root recovery for one fixed original candidate

Finite disjoint auxiliary cells pay the same physical budget once. At fixed
clipping height, omitted roots cost that height times their original mass.
Refining the original root loss therefore preserves the same candidate and
requires no finite full kinetic moment in advance.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

/-- Finite Fatou combines cell bounds along the same sample subsequence,
rather than extracting a different weak candidate on each auxiliary cell. -/
theorem fixedCandidate_sum_liminf_le_liminf_sum {I : Type*} [Fintype I]
    (f : I → ℕ → ℝ≥0∞) :
    (∑ i, liminf (f i) atTop) ≤ liminf (fun n ↦ ∑ i, f i n) atTop := by
  let _ : MeasurableSpace I := ⊤
  have hfatou := lintegral_liminf_le (μ := (Measure.count : Measure I)) (u := atTop)
    (f := fun n i ↦ f i n)
    (fun n ↦ measurable_of_countable (fun i ↦ f i n))
  simpa only [lintegral_count,tsum_fintype] using hfatou

/-- All finite cells consume one common actual upper budget at each n. -/
theorem fixedCandidate_sum_cell_liminf_le_shared_budget {I : Type*} [Fintype I]
    (cell : I → ℝ≥0∞) (f : I → ℕ → ℝ≥0∞) (budget : ℕ → ℝ≥0∞)
    (hcell : ∀ i, cell i ≤ liminf (f i) atTop)
    (hbudget : ∀ᶠ n in atTop, (∑ i, f i n) ≤ budget n) :
    (∑ i, cell i) ≤ liminf budget atTop := by
  exact (Finset.sum_le_sum (fun i _ ↦ hcell i)).trans
    ((fixedCandidate_sum_liminf_le_liminf_sum f).trans (liminf_le_liminf hbudget))

/-- Lower integrals are superadditive even before measurability of an
auxiliary finite-cell readout has been established. -/
theorem fixedCandidate_sum_lintegral_le {I Ω : Type*} [Fintype I]
    [MeasurableSpace Ω] (η : Measure Ω) (f : I → Ω → ℝ≥0∞) :
    (∑ i, ∫⁻ ω, f i ω ∂η) ≤ ∫⁻ ω, ∑ i, f i ω ∂η := by
  classical
  have h (s : Finset I) :
      (∑ i ∈ s, ∫⁻ ω, f i ω ∂η) ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂η := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
  exact h Finset.univ

/-- At every sample the same optimizer pays all disjoint root cells once.
Taking its original sampling expectation preserves that single budget. -/
theorem lintegral_expected_cavityRoot_disjoint_domains_window_sum_le
    {I Ω X ι : Type*} [Fintype I] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace X]
    (η : Measure Ω) (Γ : Ω → Measure X) [∀ ω, IsFiniteMeasure (Γ ω)]
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (upper : Ω → X → ℝ≥0∞) (hupper : ∀ ω, Measurable (upper ω))
    (rootDomain U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    (N : ℝ) (hN : 0 < N)
    (cells : I → Set (ι → ℝ)) (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j))) :
    (∑ i, ∫⁻ ω, ∫⁻ root, ENNReal.ofReal N *
      cavityRootWindowReadout (Γ ω) coord (upper ω) U root
        ∂cavityRootMeasure volume (rootDomain ∩ cells i) N ∂η) ≤
      volume U * ∫⁻ ω, ∫⁻ x, upper ω x ∂Γ ω ∂η := by
  calc
    _ ≤ ∫⁻ ω, ∑ i, ∫⁻ root, ENNReal.ofReal N *
        cavityRootWindowReadout (Γ ω) coord (upper ω) U root
          ∂cavityRootMeasure volume (rootDomain ∩ cells i) N ∂η :=
      fixedCandidate_sum_lintegral_le η _
    _ ≤ ∫⁻ ω, volume U * ∫⁻ x, upper ω x ∂Γ ω ∂η := by
      apply lintegral_mono
      intro ω
      exact lintegral_cavityRoot_disjoint_domains_window_sum_le (Γ ω) coord hcoord
        (upper ω) (hupper ω) rootDomain U hU N hN cells hmeas hdisjoint
    _ = _ := lintegral_const_mul' _ _ hUfinite

section RootMass
variable {C Y : Type*} [MeasurableSpace C] [MeasurableSpace Y]

/-- The original root mass seen by a fixed edge-Palm kernel is its actual
unnormalized total mass, never a replacement probability root law. -/
def fixedCandidateRootMass (η : Measure C) (κ : Kernel C Y) : Measure C :=
  η.withDensity (fun c ↦ κ c univ)

/-- At clipping height B, any omitted root set costs at most B times its
actual original mass. No positive lower density bound is involved. -/
theorem lintegral_fixedCandidate_clipped_on_set_le
    (η : Measure C) (κ : Kernel C Y) (E : C × Y → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ∞) (A : Set C) (hA : MeasurableSet A) :
    (∫⁻ c in A, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) ≤
      B * fixedCandidateRootMass η κ A := by
  rw [fixedCandidateRootMass,withDensity_apply _ hA]
  calc
    _ ≤ ∫⁻ c in A, B * κ c univ ∂η := by
      apply lintegral_mono
      intro c
      exact (lintegral_mono (fun y ↦ min_le_left B (E (c,y)))).trans_eq (lintegral_const B)
    _ = _ := lintegral_const_mul' B _ hB

/-- Measured disjoint cells split one fixed clipped candidate exactly; the
uncovered remainder is bounded by its original root mass only. -/
theorem lintegral_fixedCandidate_clipped_le_cells_add_root_loss
    {I : Type*} [Fintype I]
    (η : Measure C) (κ : Kernel C Y) (E : C × Y → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ∞) (K : Set C) (hK : MeasurableSet K)
    (cells : I → Set C) (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j)))
    (hsub : ∀ i, cells i ⊆ K) :
    (∫⁻ c in K, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) ≤
      (∑ i, ∫⁻ c in cells i, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) +
        B * fixedCandidateRootMass η κ (K \ ⋃ i, cells i) := by
  let U := ⋃ i, cells i
  have hU : MeasurableSet U := MeasurableSet.iUnion hmeas
  have hUK : U ⊆ K := iUnion_subset hsub
  have hd : Disjoint U (K \ U) := by
    rw [Set.disjoint_left]
    intro c hc hm
    exact hm.2 hc
  have hsplit : (∫⁻ c in K, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) =
      (∫⁻ c in U, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) +
        (∫⁻ c in K \ U, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) := by
    rw [← lintegral_union (hK.diff hU) hd,Set.union_sdiff_cancel hUK]
  rw [hsplit]
  have hsum : (∫⁻ c in U, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) =
      ∑ i, ∫⁻ c in cells i, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η := by
    simpa only [tsum_fintype] using
      lintegral_iUnion hmeas hdisjoint (fun c ↦ ∫⁻ y, min B (E (c,y)) ∂κ c)
  rw [hsum]
  exact add_le_add le_rfl
    (lintegral_fixedCandidate_clipped_on_set_le η κ E B hB (K \ U) (hK.diff hU))

/-- At each fixed B, arbitrarily fine finite root refinements recover a bound
for the SAME fixed candidate. The cells need not increase with refinement. -/
theorem lintegral_fixedCandidate_clipped_le_of_root_refinements
    (η : Measure C) (κ : Kernel C Y) (E : C × Y → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ∞) (K : Set C) (hK : MeasurableSet K)
    (I : ℕ → Type*) [∀ n, Fintype (I n)]
    (cells : ∀ n, I n → Set C) (hmeas : ∀ n i, MeasurableSet (cells n i))
    (hdisjoint : ∀ n, Pairwise (fun i j ↦ Disjoint (cells n i) (cells n j)))
    (hsub : ∀ n i, cells n i ⊆ K)
    (budget : ℝ≥0∞) (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hcover : Tendsto (fun n ↦ fixedCandidateRootMass η κ (K \ ⋃ i, cells n i)) atTop (𝓝 0))
    (hbudget : ∀ n,
      (∑ i, ∫⁻ c in cells n i, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) ≤ budget + error n) :
    (∫⁻ c in K, ∫⁻ y, min B (E (c,y)) ∂κ c ∂η) ≤ budget := by
  have hmissing := ENNReal.Tendsto.const_mul hcover (Or.inr hB)
  have hlim : Tendsto (fun n ↦ budget + error n +
      B * fixedCandidateRootMass η κ (K \ ⋃ i, cells n i)) atTop (𝓝 budget) := by
    simpa only [add_zero,mul_zero] using (tendsto_const_nhds.add herror).add hmissing
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
  intro n
  exact (lintegral_fixedCandidate_clipped_le_cells_add_root_loss η κ E B hB K hK
    (cells n) (hmeas n) (hdisjoint n) (hsub n)).trans (add_le_add (hbudget n) le_rfl)

end RootMass

section ActualPalmKernel
variable {C : Type*} [MeasurableSpace C] {q : ℕ}

/-- The original whole-scene kernel supplies a measurable raw edge-Palm
kernel without a pointwise choice or normalization of its theta mass. -/
def originalIIDRawPairPalmKernel
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) :
    Kernel C (PhysicalPairPalmMark (Fin q)) :=
  ((physicalScenePairKernel ∘ₖ (Λ.map Prod.fst)).restrict
    ((measurableSet_palmUnitCube (Fin q)).prod MeasurableSet.univ)).map Prod.snd

instance originalIIDRawPairPalmKernelIsSFinite
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsSFiniteKernel Λ] :
    IsSFiniteKernel (originalIIDRawPairPalmKernel Λ) := by
  unfold originalIIDRawPairPalmKernel
  infer_instance

@[simp]
theorem originalIIDRawPairPalmKernel_apply
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) (c : C) :
    originalIIDRawPairPalmKernel Λ c = cubePalm (Fin q)
      (physicalScenePairCampbell ((Λ c).map Prod.fst)) := by
  rw [originalIIDRawPairPalmKernel,Kernel.map_apply _ measurable_snd,
    Kernel.restrict_apply,Kernel.comp_apply,Kernel.map_apply _ measurable_fst]
  rfl

/-- The proved actual full-matching profile identifies the raw Palm root
mass with the original intensity, including roots of intensity zero. -/
theorem fixedCandidateRootMass_of_original_matching_profile
    (η : Measure C) (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q)))
    (gap : ℝ) (θ : C → ℝ) (α β : C → Measure ℝ)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (input : C → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (hθ : ∀ᵐ c ∂η, 0 ≤ θ c)
    (hprofile : ∀ᵐ c ∂η, OriginalIIDConditionalMatchingProfile gap (θ c)
      (α c) (β c) (input c) (Λ c)) :
    fixedCandidateRootMass η (originalIIDRawPairPalmKernel Λ) =
      η.withDensity (fun c ↦ ENNReal.ofReal (θ c)) := by
  apply withDensity_congr_ae
  filter_upwards [hθ,hprofile] with c hc hp
  rw [originalIIDRawPairPalmKernel_apply]
  exact (original_raw_palm_data_of_matching_profile q gap (θ c) hc
    (α c) (β c) (input c) (Λ c) hp).2.2

end ActualPalmKernel

/-- Exact coordinate-density mass on a measured native cell. The finite
native density is converted to real values only on this retained cell. -/
theorem lintegral_coordinate_density_image_eq_native_mass
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {q : ℕ}
    (κ : Measure V) (e : V ≃L[ℝ] (Fin q → ℝ)) (c : ℝ≥0)
    (hmap : κ.map e = (c : ℝ≥0∞) • (volume : Measure (Fin q → ℝ)))
    (density : V → ℝ≥0∞) (hdensity : Measurable density)
    (A : Set V) (hA : MeasurableSet A) (hfinite : ∀ w ∈ A, density w ≠ ∞) :
    (∫⁻ x in e '' A, ENNReal.ofReal ((c : ℝ) * (density (e.symm x)).toReal)
      ∂(volume : Measure (Fin q → ℝ))) =
        ((κ.restrict A).withDensity density) univ := by
  have hrestricted : (κ.restrict A).map e =
      (c : ℝ≥0∞) • (volume : Measure (Fin q → ℝ)).restrict (e '' A) := by
    calc
      _ = (κ.map e).restrict (e '' A) := by
        have he := e.toHomeomorph.measurableEmbedding.restrict_map κ (e '' A)
        change (κ.map e).restrict (e '' A) =
          (κ.restrict (e ⁻¹' (e '' A))).map e at he
        simpa only [preimage_image_eq _ e.injective] using he.symm
      _ = _ := by rw [hmap,Measure.restrict_smul]
  have himage : MeasurableSet (e '' A) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  calc
    _ = ∫⁻ x in e '' A, (c : ℝ≥0∞) * density (e.symm x) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem himage] with x hx
      obtain ⟨w,hw,rfl⟩ := hx
      rw [e.symm_apply_apply,ENNReal.ofReal_mul c.coe_nonneg,
        ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_toReal (hfinite w hw)]
    _ = ∫⁻ x, density (e.symm x) ∂((κ.restrict A).map e) := by
      rw [hrestricted,lintegral_smul_measure]
      exact lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = _ := by
      simpa only [e.symm_apply_apply] using lintegral_map
        (f := fun x ↦ density (e.symm x))
        (hdensity.comp e.symm.continuous.measurable) e.continuous.measurable

section OriginalRootMass
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The exact standard-coordinate intensity integrates to the original label
mass on every measurable part of this SAME retained core. -/
theorem PopulationHaarPressureCore.original_coordinate_intensity_mass
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    (∫⁻ c in e '' (R '' L), ENNReal.ofReal
      ((originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) * (density (e.symm c)).toReal)
      ∂volume) = lambda L := by
  intro C S e R density
  let _rootRecoveryMetric : MetricSpace M := F.metricSpace
  let _rootRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootRecoveryPolish : PolishSpace M := inferInstance
  let _rootRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  have hsub' : L ⊆ (D.intensity i).roots := by rwa [D.intensity_roots]
  have himage : MeasurableSet (R '' L) :=
    D.measurable_cell_label_image hcomplete i hL hsub
  have hfinite (w) (hw : w ∈ R '' L) : density w ≠ (∞ : ℝ≥0∞) := by
    obtain ⟨z,hz,rfl⟩ := hw
    rw [show density (R z) = populationSeedPieceRootDensity P a κ lambda C.seedIndex z from
      populationSeedPieceHaarDensity_at_root P a κ lambda hF hcomplete hu ha hinj
        C.seedIndex (C.roots_subset_piece (hsub hz))]
    exact ((D.intensity i).finite_density z (hsub' hz)).ne
  calc
    _ = (((κ C.seedIndex).restrict (R '' L)).withDensity density) univ :=
      lintegral_coordinate_density_image_eq_native_mass (κ C.seedIndex) e
        (originalSeedCoordinateHaarFactor S (κ C.seedIndex))
        (map_originalSeedHaar_eq_coordinate_volume S (κ C.seedIndex)) density
        (measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj C.seedIndex)
        (R '' L) himage hfinite
    _ = _ := (D.cell_masses hF hcomplete hu ha hinj i hL hsub).1

/-- The original lambda restriction pushes to its exact standard-coordinate
intensity. Consequently weighted lambda and volume readouts use the same
Haar Jacobian, rather than identifying their density powers informally. -/
theorem PopulationHaarPressureCore.map_original_label_eq_coordinate_intensity
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    (lambda.restrict C.roots).map (fun z ↦ e (R z)) =
      (volume.restrict (e '' (R '' C.roots))).withDensity (fun c ↦ ENNReal.ofReal
        ((originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
          (density (e.symm c)).toReal)) := by
  intro C S e R density
  let _rootRecoveryMetric : MetricSpace M := F.metricSpace
  let _rootRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootRecoveryPolish : PolishSpace M := inferInstance
  let _rootRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  have hcoord : Measurable (fun z ↦ e (R z)) := e.continuous.measurable.comp
    (measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj)
  ext A hA
  let L := (fun z ↦ e (R z)) ⁻¹' A ∩ C.roots
  have hL : MeasurableSet L := (hA.preimage hcoord).inter C.roots_compact.measurableSet
  have himage : e '' (R '' L) = A ∩ (e '' (R '' C.roots)) := by
    simpa only [L,image_image] using image_preimage_inter (fun z ↦ e (R z)) C.roots A
  rw [Measure.map_apply hcoord hA,Measure.restrict_apply (hA.preimage hcoord),
    withDensity_apply _ hA,Measure.restrict_restrict hA]
  exact (D.original_coordinate_intensity_mass hF hcomplete hu ha hinj i hL
    (inter_subset_right : L ⊆ C.roots)).symm.trans (by rw [himage])

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure] in
/-- The stored original root identity makes the old seed coordinates
injective on its complete retained core, including the boundary. -/
theorem PopulationHaarPressureCore.original_coordinate_injOn
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    InjOn (fun z ↦ e (R z)) C.roots := by
  intro C S e R z hz z' hz' he
  have he' : R z = R z' := e.injective he
  have hzI : z ∈ (D.intensity i).roots := (D.intensity_roots i).symm ▸ hz
  have hzI' : z' ∈ (D.intensity i).roots := (D.intensity_roots i).symm ▸ hz'
  calc
    z = a (S.curve (R z) 0) := ((D.intensity i).root_identity z hzI).symm
    _ = z' := by rw [he']; exact (D.intensity i).root_identity z' hzI'

/-- Refining the old coordinate core by ANY auxiliary original core loses
at most that auxiliary core's stored original lambda loss. Coordinates and
the intensity remain those of the old fixed candidate. -/
theorem PopulationHaarPressureCore.original_coordinate_uncovered_mass_lt
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count)
    {Good' : (ℚ → M) → Prop} {r' : ℝ} {δ' loss' : ℝ≥0∞}
    (D' : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good' r' δ' loss') :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let K := e '' (R '' C.roots)
    let cells := fun j : Fin D'.continuous.count ↦
      e '' (R '' (C.roots ∩ (D'.continuous.coefficient j).roots))
    (∫⁻ c in K \ ⋃ j, cells j, ENNReal.ofReal
      ((originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) * (density (e.symm c)).toReal)
      ∂volume) < loss' := by
  intro C S e R density K cells
  let _rootRecoveryMetric : MetricSpace M := F.metricSpace
  let _rootRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootRecoveryPolish : PolishSpace M := inferInstance
  let _rootRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  have hR : InjOn (fun z ↦ e (R z)) C.roots := D.original_coordinate_injOn i
  have hset : (fun z ↦ e (R z)) '' (C.roots \ D'.continuous.population.roots) =
      K \ ⋃ j, cells j := by
    rw [hR.image_sdiff,← D'.continuous.union_eq,inter_iUnion,image_iUnion]
    simp only [K,cells,image_image]
  have hL : MeasurableSet (C.roots \ D'.continuous.population.roots) :=
    C.roots_compact.measurableSet.diff D'.continuous.population.compact.measurableSet
  have hm := D.original_coordinate_intensity_mass hF hcomplete hu ha hinj i hL
    (sdiff_subset : C.roots \ D'.continuous.population.roots ⊆ C.roots)
  change (∫⁻ c in e '' (R '' (C.roots \ D'.continuous.population.roots)),
    ENNReal.ofReal ((originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
      (density (e.symm c)).toReal) ∂volume) = _ at hm
  rw [show K \ ⋃ j, cells j = e '' (R '' (C.roots \ D'.continuous.population.roots)) from
    hset.symm.trans (image_image e R _).symm,hm]
  exact (measure_mono (fun z hz ↦ hz.2)).trans_lt D'.continuous.population.complement_small

/-- The SAME whole-core matching kernel has exactly the original lambda
mass on any measured subset of its retained roots. Its actual profile is an
upstream fact; no Palm normalization or kinetic moment is assumed. -/
theorem PopulationHaarPressureCore.fixed_candidate_raw_palm_mass_eq_label
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ) (α β : (Fin q → ℝ) → Measure ℝ)
      (_ : ∀ c, IsProbabilityMeasure (α c)) (_ : ∀ c, IsProbabilityMeasure (β c))
      (input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
        LocalFiniteMeasure (LegalMarkedPhysicalPoint q))),
      (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
          (α c) (β c) (input c) (Λ c)) →
      ∀ {L : Set (ℚ → M)}, MeasurableSet L → L ⊆ C.roots →
        fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ) (e '' (R '' L)) =
          lambda L := by
  intro C S q e R K ref Λ gap α β hα hβ input hprofile L hL hsub
  let _rootRecoveryMetric : MetricSpace M := F.metricSpace
  let _rootRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootRecoveryPolish : PolishSpace M := inferInstance
  let _rootRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  let (c : Fin q → ℝ) : IsProbabilityMeasure (α c) := hα c
  let (c : Fin q → ℝ) : IsProbabilityMeasure (β c) := hβ c
  have hA : MeasurableSet (e '' (R '' L)) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D.measurable_cell_label_image hcomplete i hL hsub)
  have hpA := ae_restrict_of_ae_restrict_of_subset (image_mono (image_mono hsub)) hprofile
  rw [fixedCandidateRootMass,withDensity_apply _ hA]
  calc
    _ = ∫⁻ c in e '' (R '' L), ENNReal.ofReal
        ((originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
          (populationSeedPieceHaarDensity P a κ lambda C.seedIndex (e.symm c)).toReal)
        ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hA,hpA] with c hc hp
      obtain ⟨w,⟨z,hz,hRz⟩,hew⟩ := hc
      have hec : e (R z) = c := (congrArg e hRz).trans hew
      have href : ref c = z := by
        rw [← hec]
        dsimp only [ref]
        rw [e.symm_apply_apply]
        exact (D.intensity i).root_identity z ((D.intensity_roots i).symm ▸ hsub hz)
      have hRref : R (ref c) = e.symm c := by
        apply e.injective
        rw [e.apply_symm_apply,href]
        exact hec
      have hθ : 0 ≤ originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c) :=
        mul_nonneg (NNReal.coe_nonneg _)
          (populationAtlasTheta_nonneg P a κ lambda C.seedIndex (ref c))
      rw [originalIIDRawPairPalmKernel_apply,
        (original_raw_palm_data_of_matching_profile q gap _ hθ
          (α c) (β c) (input c) (Λ c) hp).2.2]
      change ENNReal.ofReal ((originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
        (populationSeedPieceHaarDensity P a κ lambda C.seedIndex (R (ref c))).toReal) = _
      rw [hRref]
    _ = _ := D.original_coordinate_intensity_mass hF hcomplete hu ha hinj i hL hsub

/-- At each fixed finite B, roots omitted by an auxiliary original core
cost at most B times its STORED lambda loss for the SAME raw candidate.
The auxiliary cells do not select new weak limits or alter the old kernel. -/
theorem PopulationHaarPressureCore.fixed_candidate_clipped_uncovered_le_aux_loss
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count)
    {Good' : (ℚ → M) → Prop} {r' : ℝ} {δ' loss' : ℝ≥0∞}
    (D' : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good' r' δ' loss') :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let cells := fun j : Fin D'.continuous.count ↦
      e '' (R '' (C.roots ∩ (D'.continuous.coefficient j).roots))
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ) (α β : (Fin q → ℝ) → Measure ℝ)
      (_ : ∀ c, IsProbabilityMeasure (α c)) (_ : ∀ c, IsProbabilityMeasure (β c))
      (input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
        LocalFiniteMeasure (LegalMarkedPhysicalPoint q))),
      (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
          (α c) (β c) (input c) (Λ c)) →
      ∀ (E : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞)
        (B : ℝ≥0∞), B ≠ (∞ : ℝ≥0∞) →
        (∫⁻ c in K \ ⋃ j, cells j, ∫⁻ y, min B (E (c,y))
          ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤ B * loss' := by
  intro C S q e R K ref cells Λ gap α β hα hβ input hprofile E B hB
  let _rootRecoveryMetric : MetricSpace M := F.metricSpace
  let _rootRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootRecoveryPolish : PolishSpace M := inferInstance
  let _rootRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  let L := C.roots \ D'.continuous.population.roots
  have hL : MeasurableSet L :=
    C.roots_compact.measurableSet.diff D'.continuous.population.compact.measurableSet
  have hsub : L ⊆ C.roots := sdiff_subset
  have hset : e '' (R '' L) = K \ ⋃ j, cells j := by
    have hR : InjOn (fun z ↦ e (R z)) C.roots := D.original_coordinate_injOn i
    change e '' (R '' (C.roots \ D'.continuous.population.roots)) = _
    rw [image_image,hR.image_sdiff,← D'.continuous.union_eq,inter_iUnion,image_iUnion]
    simp only [K,cells,image_image]
  have hmass := D.fixed_candidate_raw_palm_mass_eq_label hF hcomplete hu ha hinj i
    Λ gap α β hα hβ input hprofile hL hsub
  have hA : MeasurableSet (e '' (R '' L)) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D.measurable_cell_label_image hcomplete i hL hsub)
  rw [← hset]
  exact (lintegral_fixedCandidate_clipped_on_set_le volume
    (originalIIDRawPairPalmKernel Λ) E B hB _ hA).trans
      (by
        rw [hmass]
        have hloss : lambda L ≤ loss' := (measure_mono (fun z hz ↦ hz.2)).trans
          D'.continuous.population.complement_small.le
        gcongr)

/-- Actual auxiliary cores with vanishing STORED lambda loss exhaust each
fixed clipping of one old candidate. Only the finite-cell energy estimates
remain to be supplied; no root-coverage or kinetic-integrability oracle is
required, and neither the old kernel nor its sample subsequence changes. -/
theorem PopulationHaarPressureCore.fixed_candidate_clipped_le_of_auxiliary_cores
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count)
    (Good' : ℕ → (ℚ → M) → Prop) (r' : ℕ → ℝ) (δ' loss' : ℕ → ℝ≥0∞)
    (D' : ∀ n, PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (Good' n) (r' n) (δ' n) (loss' n))
    (hloss : Tendsto loss' atTop (𝓝 0)) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let cells := fun n (j : Fin (D' n).continuous.count) ↦
      e '' (R '' (C.roots ∩ ((D' n).continuous.coefficient j).roots))
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ) (α β : (Fin q → ℝ) → Measure ℝ)
      (_ : ∀ c, IsProbabilityMeasure (α c)) (_ : ∀ c, IsProbabilityMeasure (β c))
      (input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
        LocalFiniteMeasure (LegalMarkedPhysicalPoint q))),
      (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
          (α c) (β c) (input c) (Λ c)) →
      ∀ (E : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞)
        (B : ℝ≥0∞), B ≠ (∞ : ℝ≥0∞) →
      ∀ (budget : ℝ≥0∞) (error : ℕ → ℝ≥0∞), Tendsto error atTop (𝓝 0) →
        (∀ n, (∑ j, ∫⁻ c in cells n j, ∫⁻ y, min B (E (c,y))
          ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤ budget + error n) →
        (∫⁻ c in K, ∫⁻ y, min B (E (c,y))
          ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤ budget := by
  intro C S q e R K ref cells Λ gap α β hα hβ input hprofile E B hB budget error herror hbudget
  let _rootRecoveryMetric : MetricSpace M := F.metricSpace
  let _rootRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootRecoveryPolish : PolishSpace M := inferInstance
  let _rootRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  have hK : MeasurableSet K := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    (D.measurable_cell_label_image hcomplete i C.roots_compact.measurableSet Subset.rfl)
  have hmeas (n) (j) : MeasurableSet (cells n j) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D.measurable_cell_label_image hcomplete i
        (C.roots_compact.measurableSet.inter
          ((D' n).continuous.coefficient j).roots_compact.measurableSet) inter_subset_left)
  have hdisjoint (n) : Pairwise (fun j k ↦ Disjoint (cells n j) (cells n k)) := by
    intro j k hjk
    change Disjoint (e '' (R '' _)) (e '' (R '' _))
    simp only [image_image]
    exact (((D' n).continuous.disjoint hjk).mono inter_subset_right inter_subset_right).image
      (D.original_coordinate_injOn i) inter_subset_left inter_subset_left
  have hsub (n) (j) : cells n j ⊆ K := image_mono (image_mono inter_subset_left)
  have htail (n) : fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)
      (K \ ⋃ j, cells n j) ≤ loss' n := by
    have hm := D.fixed_candidate_clipped_uncovered_le_aux_loss hF hcomplete hu ha hinj i (D' n)
      Λ gap α β hα hβ input hprofile (fun _ ↦ 1) 1 (by simp)
    rw [fixedCandidateRootMass,withDensity_apply _ (hK.diff (MeasurableSet.iUnion (hmeas n)))]
    simpa only [min_self,lintegral_one,one_mul] using hm
  have hcover : Tendsto (fun n ↦ fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)
      (K \ ⋃ j, cells n j)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hloss (fun _ ↦ bot_le) htail
  exact lintegral_fixedCandidate_clipped_le_of_root_refinements volume
    (originalIIDRawPairPalmKernel Λ) E B hB K hK
    (fun n ↦ Fin (D' n).continuous.count) cells hmeas hdisjoint hsub
    budget error herror hcover hbudget

end OriginalRootMass
end OTSelector.Reconstruction
