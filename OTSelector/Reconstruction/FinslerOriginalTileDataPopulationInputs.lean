import OTSelector.Probability.FinslerAtlasCubeInputs
import OTSelector.Reconstruction.FinslerMeasuredAtlas

/-!
# Population and Haar law inputs of the canonical Finsler tile data

The upper pressure localization
`OTSelector/Reconstruction/FinslerOriginalIIDPressureUpperLocalization.lean`
consumes, for a finite family of tiles, five population-level law inputs:

* exact cell masses `μ (cellS ⁻¹' {c}) = ofReal (w c)` and the same for `ν`;
* the normalized cube-coordinate law `cubeMeasure (Fin q) 1` on every cell;
* the normalized mark laws `α c` and `β c` on every cell;
* independence of the cube coordinate and the mark on every cell.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open MeasureTheory.Measure
open OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
  unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## Exact cell masses from a common label map -/

section CellMasses

variable {Z : Type*} [MeasurableSpace Z] {ι : Type*} [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **Physical cell mass equals label mass.**  A cell of the physical space that
is the preimage under the common label map of a measurable set of labels has
physical mass exactly the label mass. -/
theorem cell_mass_eq_label_mass (a : M → Z) (ha : Measurable a) (μ : Measure M)
    (lambda : Measure Z) (hμa : μ.map a = lambda) (cellZ : Z → ι)
    (hcellZ : Measurable cellZ) (c : ι) :
    μ ((fun x => cellZ (a x)) ⁻¹' {c}) = lambda (cellZ ⁻¹' {c}) := by
  rw [show (fun x => cellZ (a x)) ⁻¹' {c} = a ⁻¹' (cellZ ⁻¹' {c}) from rfl,
    ← hμa, Measure.map_apply ha (hcellZ (measurableSet_singleton c))]

/-- **Exact cell mass in the upper-localization form.**  The physical cell mass is
the `ofReal` of the cell weight, where the weight is the label mass of the index
set. -/
theorem cell_mass_eq_ofReal_label_mass (a : M → Z) (ha : Measurable a)
    {μ : Measure M} [IsFiniteMeasure μ] {lambda : Measure Z} [IsFiniteMeasure lambda]
    (hμa : μ.map a = lambda)
    (cellZ : Z → ι) (hcellZ : Measurable cellZ) (c : ι) :
    μ ((fun x => cellZ (a x)) ⁻¹' {c}) =
      ENNReal.ofReal ((lambda (cellZ ⁻¹' {c})).toReal) := by
  rw [cell_mass_eq_label_mass a ha μ lambda hμa cellZ hcellZ c,
    ENNReal.ofReal_toReal (measure_ne_top lambda _)]

/-- **The two colours have exactly equal cell masses.**  This is the exact
balance `μ.map a = ν.map a` of the measured atlas. -/
theorem cell_masses_eq_both_colours (a : M → Z) (ha : Measurable a)
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {lambda : Measure Z} [IsFiniteMeasure lambda]
    (hμa : μ.map a = lambda) (hνa : ν.map a = lambda)
    (cellZ : Z → ι) (hcellZ : Measurable cellZ) (c : ι) :
    μ ((fun x => cellZ (a x)) ⁻¹' {c}) = ν ((fun x => cellZ (a x)) ⁻¹' {c}) ∧
      μ ((fun x => cellZ (a x)) ⁻¹' {c}) =
        ENNReal.ofReal ((lambda (cellZ ⁻¹' {c})).toReal) :=
  ⟨by rw [cell_mass_eq_label_mass a ha μ lambda hμa cellZ hcellZ c,
        cell_mass_eq_label_mass a ha ν lambda hνa cellZ hcellZ c],
    cell_mass_eq_ofReal_label_mass a ha hμa cellZ hcellZ c⟩

/-- **The tile weights are a probability vector.**  A measurable index of a
probability label space partitions it into cells whose label masses sum to one;
consequently the corresponding tile weights do. -/
theorem sum_cellWeight_eq_one (lambda : Measure Z) [IsProbabilityMeasure lambda]
    (cellZ : Z → ι) (hcellZ : Measurable cellZ) :
    ∑ c, (lambda (cellZ ⁻¹' {c})).toReal = 1 := by
  have hmeas : ∀ c, MeasurableSet (cellZ ⁻¹' {c}) := fun c =>
    hcellZ (measurableSet_singleton c)
  have hdisj : Pairwise (Disjoint on fun c => cellZ ⁻¹' ({c} : Set ι)) := by
    intro c c' hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    exact hne (by simpa using hz.symm.trans hz')
  have hunion : (⋃ c, cellZ ⁻¹' ({c} : Set ι)) = univ := by
    ext z
    simp only [mem_iUnion, mem_preimage, mem_singleton_iff, mem_univ, iff_true]
    exact ⟨cellZ z, rfl⟩
  have hsum : lambda (⋃ c, cellZ ⁻¹' ({c} : Set ι)) =
      ∑ c, lambda (cellZ ⁻¹' {c}) := by
    simpa only [tsum_fintype] using measure_iUnion (μ := lambda)
      (f := fun c => cellZ ⁻¹' ({c} : Set ι)) hdisj hmeas
  rw [← ENNReal.toReal_sum (fun c _ => measure_ne_top lambda _), ← hsum,
    hunion, measure_univ, ENNReal.toReal_one]

/-- **Positive weights give positive label masses.** -/
theorem cell_label_mass_pos (lambda : Measure Z) [IsFiniteMeasure lambda]
    (cellZ : Z → ι) (c : ι) (hw : 0 < (lambda (cellZ ⁻¹' {c})).toReal) :
    0 < lambda (cellZ ⁻¹' {c}) := by
  rw [pos_iff_ne_zero]
  intro h
  rw [h] at hw
  exact lt_irrefl (0 : ℝ) hw

end CellMasses

/-! ## Transport of label-space cell laws to the physical population -/

section CellLawTransfer

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]

/-- **General transport of a normalized cell law.**  If a physical observation
`gS` agrees almost everywhere on a physical cell with a label-level observation
`gZ` composed with the common label map, then the normalized physical cell law
of `gS` is the normalized label cell law of `gZ`. -/
theorem normalized_cell_map_eq_of_label (a : M → Z) (ha : Measurable a)
    (η : Measure M) (lambda : Measure Z) (hηa : η.map a = lambda)
    {K : Set Z} (hK : MeasurableSet K) {D : Type*} [MeasurableSpace D]
    (gS : M → D) (gZ : Z → D) (hgZ : Measurable gZ)
    (hagree : gS =ᵐ[η.restrict (a ⁻¹' K)] fun x => gZ (a x)) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map gS =
      ((lambda K)⁻¹ • lambda.restrict K).map gZ := by
  have hmass : η (a ⁻¹' K) = lambda K := by
    rw [← hηa, Measure.map_apply ha hK]
  rw [hmass]
  have h1 : ((lambda K)⁻¹ • η.restrict (a ⁻¹' K)).map gS =
      ((lambda K)⁻¹ • η.restrict (a ⁻¹' K)).map (fun x => gZ (a x)) := by
    rw [Measure.map_smul, Measure.map_smul, Measure.map_congr hagree]
  rw [h1, Measure.map_smul, Measure.map_smul]
  congr 1
  calc Measure.map (fun x => gZ (a x)) (η.restrict (a ⁻¹' K))
      = Measure.map (gZ ∘ a) (η.restrict (a ⁻¹' K)) := rfl
    _ = Measure.map gZ (Measure.map a (η.restrict (a ⁻¹' K))) := (Measure.map_map hgZ ha).symm
    _ = Measure.map gZ (lambda.restrict K) := by
        rw [OTSelector.Probability.map_restrict_preimage_eq η a lambda ha hηa hK]

/-- **Physical normalized cube-coordinate law from the label-level cube law.** -/
theorem cell_cube_law_of_label_law (a : M → Z) (ha : Measurable a)
    (η : Measure M) (lambda : Measure Z) (hηa : η.map a = lambda)
    {K : Set Z} (hK : MeasurableSet K) {q : ℕ}
    (coordS : M → Fin q → ℝ) (coordZ : Z → Fin q → ℝ) (hcoordZ : Measurable coordZ)
    (hcubeZ : ((lambda K)⁻¹ • lambda.restrict K).map coordZ =
      OTSelector.Probability.cubeMeasure (Fin q) 1)
    (hagree : coordS =ᵐ[η.restrict (a ⁻¹' K)] fun x => coordZ (a x)) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map coordS =
      OTSelector.Probability.cubeMeasure (Fin q) 1 := by
  rw [normalized_cell_map_eq_of_label a ha η lambda hηa hK coordS coordZ hcoordZ hagree, hcubeZ]

/-- **Physical normalized mark law from the label-level mark law.** -/
theorem cell_mark_law_of_label_law (a : M → Z) (ha : Measurable a)
    (η : Measure M) (lambda : Measure Z) (hηa : η.map a = lambda)
    {K : Set Z} (hK : MeasurableSet K) {Am : Type*} [MeasurableSpace Am]
    (labelS : M → Am) (markZ : Z → Am) (hmarkZ : Measurable markZ) (α : Measure Am)
    (hmarkLaw : ((lambda K)⁻¹ • lambda.restrict K).map markZ = α)
    (hagree : labelS =ᵐ[η.restrict (a ⁻¹' K)] fun x => markZ (a x)) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map labelS = α := by
  rw [normalized_cell_map_eq_of_label a ha η lambda hηa hK labelS markZ hmarkZ hagree, hmarkLaw]

/-- **Physical independence from label-level independence.**  Independence of the
cube coordinate and the mark on the normalized label cell law transfers to the
normalized physical cell law. -/
theorem cell_indep_of_label_indep (a : M → Z) (ha : Measurable a)
    (η : Measure M) [IsFiniteMeasure η] (lambda : Measure Z) [IsFiniteMeasure lambda]
    (hηa : η.map a = lambda)
    {K : Set Z} (hK : MeasurableSet K) {q : ℕ} {Am : Type*} [MeasurableSpace Am]
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → Am) (hlabelS : Measurable labelS)
    (coordZ : Z → Fin q → ℝ) (hcoordZ : Measurable coordZ)
    (markZ : Z → Am) (hmarkZ : Measurable markZ)
    (hindep : IndepFun coordZ markZ ((lambda K)⁻¹ • lambda.restrict K))
    (hagreeC : coordS =ᵐ[η.restrict (a ⁻¹' K)] fun x => coordZ (a x))
    (hagreeM : labelS =ᵐ[η.restrict (a ⁻¹' K)] fun x => markZ (a x)) :
    IndepFun coordS labelS ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) := by
  haveI hfinL : IsFiniteMeasure ((lambda K)⁻¹ • lambda.restrict K) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    by_cases h : lambda K = 0
    · simp [h]
    · rw [ENNReal.inv_mul_cancel h (measure_ne_top lambda K)]
      exact ENNReal.one_lt_top
  haveI hfinE : IsFiniteMeasure ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    by_cases h : η (a ⁻¹' K) = 0
    · simp [h]
    · rw [ENNReal.inv_mul_cancel h (measure_ne_top η (a ⁻¹' K))]
      exact ENNReal.one_lt_top
  have hpair : (fun x => (coordS x, labelS x)) =ᵐ[η.restrict (a ⁻¹' K)]
      (fun x => (coordZ (a x), markZ (a x))) := by
    filter_upwards [hagreeC, hagreeM] with x hx hy
    rw [hx, hy]
  have hmapPair : ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map
      (fun x => (coordS x, labelS x)) =
      ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map
        (fun x => (coordZ (a x), markZ (a x))) := by
    rw [Measure.map_smul, Measure.map_smul, Measure.map_congr hpair]
  have hprod := hindep.map_prod_eq_prod_map_map hcoordZ.aemeasurable hmarkZ.aemeasurable
  have hcube := normalized_cell_map_eq_of_label a ha η lambda hηa hK coordS coordZ hcoordZ hagreeC
  have hmark := normalized_cell_map_eq_of_label a ha η lambda hηa hK labelS markZ hmarkZ hagreeM
  have hmapa : Measure.map a ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) =
      (lambda K)⁻¹ • lambda.restrict K := by
    have hmass : η (a ⁻¹' K) = lambda K := by
      rw [← hηa, Measure.map_apply ha hK]
    rw [hmass, Measure.map_smul,
      OTSelector.Probability.map_restrict_preimage_eq η a lambda ha hηa hK]
  refine (indepFun_iff_map_prod_eq_prod_map_map hcoordS.aemeasurable
    hlabelS.aemeasurable).mpr ?_
  calc Measure.map (fun x => (coordS x, labelS x))
        ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K))
      = Measure.map (fun x => (coordZ (a x), markZ (a x)))
          ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) := hmapPair
    _ = Measure.map (fun z => (coordZ z, markZ z))
          ((lambda K)⁻¹ • lambda.restrict K) := by
        rw [show (fun x => (coordZ (a x), markZ (a x))) =
            (fun z => (coordZ z, markZ z)) ∘ a from rfl,
          (Measure.map_map (hcoordZ.prodMk hmarkZ) ha).symm, hmapa]
    _ = (Measure.map coordS ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K))).prod
          (Measure.map labelS ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K))) := by
        rw [hprod, hcube, hmark]

/-- **The three cell law inputs from the joint product law.**  If the normalized
label cell law pushes forward under the atlas mark map to the product of the
uniform cube law and the mark law, then the physical normalized cell law has the
uniform cube coordinate law, the mark law, and independence. -/
theorem cell_law_inputs_of_label_product_law (a : M → Z) (ha : Measurable a)
    (η : Measure M) [IsFiniteMeasure η] (lambda : Measure Z) [IsFiniteMeasure lambda]
    (hηa : η.map a = lambda)
    {K : Set Z} (hK : MeasurableSet K) {q : ℕ} {Am : Type*} [MeasurableSpace Am]
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → Am) (hlabelS : Measurable labelS)
    (coordZ : Z → Fin q → ℝ) (hcoordZ : Measurable coordZ)
    (markZ : Z → Am) (hmarkZ : Measurable markZ) (α : Measure Am) [IsProbabilityMeasure α]
    (hprod : ((lambda K)⁻¹ • lambda.restrict K).map
        (fun z => (coordZ z, markZ z)) =
      (OTSelector.Probability.cubeMeasure (Fin q) 1).prod α)
    (hagreeC : coordS =ᵐ[η.restrict (a ⁻¹' K)] fun x => coordZ (a x))
    (hagreeM : labelS =ᵐ[η.restrict (a ⁻¹' K)] fun x => markZ (a x)) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map coordS =
        OTSelector.Probability.cubeMeasure (Fin q) 1 ∧
      ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map labelS = α ∧
      IndepFun coordS labelS ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) := by
  haveI hfinL : IsFiniteMeasure ((lambda K)⁻¹ • lambda.restrict K) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    by_cases h : lambda K = 0
    · simp [h]
    · rw [ENNReal.inv_mul_cancel h (measure_ne_top lambda K)]
      exact ENNReal.one_lt_top
  obtain ⟨hcubeZ, hmarkZ_law, hindepZ⟩ :=
    OTSelector.Probability.three_reductions_of_map_prod_eq_prod hcoordZ hmarkZ hprod
  exact ⟨cell_cube_law_of_label_law a ha η lambda hηa hK coordS coordZ hcoordZ
      hcubeZ hagreeC,
    cell_mark_law_of_label_law a ha η lambda hηa hK labelS markZ hmarkZ α
      hmarkZ_law hagreeM,
    cell_indep_of_label_indep a ha η lambda hηa hK coordS hcoordS labelS hlabelS
      coordZ hcoordZ markZ hmarkZ hindepZ hagreeC hagreeM⟩

end CellLawTransfer


/-! ## The measured atlas supplies a common label law -/

/-- **The measured calibrated atlas of both original populations.**  This extracts
from `exists_finsler_measured_calibrated_atlas` the common measurable label map
carrying both populations, which is the population input behind the exact cell
masses. -/
theorem exists_measured_atlas_common_label_law
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    ∃ (a : M → (ℚ → M)), Measurable a ∧ μ.map a = ν.map a := by
  let _instCommonLabelMetric : MetricSpace M := F.metricSpace
  let _instCommonLabelProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCommonLabelBorel : StandardBorelSpace M := inferInstance
  let _instCommonLabelNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, a, _hu, _hN, _hμN, _hνN, ha, _hinj, _horder, hbalance, _hface,
    _hμI, _hνI, _hμjoint, _hνjoint, _hcond, _ι, _hι, _P, _hcover⟩ :=
    exists_finsler_measured_calibrated_atlas (F := F) hF hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  exact ⟨a, ha, hbalance⟩

/-! ## The Haar/cube coordinate law of an actual atlas cell -/

/-- **Physical normalized cube-coordinate law of an atlas cell.**

For a retained label cell `K` of an atlas window `j` whose normalized seed-label
image is the unit cube, the Haar instance of the seed label measure and the
uniformity of the population density on the window piece imply that the
normalized *physical* cell law of the atlas cube coordinate is the uniform cube
law.  The physical coordinate `coordS` only has to agree with the atlas
coordinate composed with the common label map almost everywhere on the cell;
this is what allows one global piecewise-defined coordinate for all tiles. -/
theorem measured_atlas_cell_cube_law
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCubeMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {q : ℕ} (j : ℕ) [IsAddHaarMeasure (κ j)]
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j))
    (himage : e '' (populationSeedRootLabelValue (P j).seed a '' K) =
      OTSelector.Probability.seedUnitCube q)
    (η : Measure M) (hηa : η.map a = lambda)
    (coordS : M → Fin q → ℝ)
    (hagree : coordS =ᵐ[η.restrict (a ⁻¹' K)] fun x =>
      atlasSeedCoord (P j).seed e a (a x)) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map coordS =
      OTSelector.Probability.cubeMeasure (Fin q) 1 := by
  refine cell_cube_law_of_label_law a ha η lambda hηa hK coordS
    (atlasSeedCoord (P j).seed e a)
    (measurable_atlasSeedCoord (P j).seed hF hcomplete hu ha hinj e) ?_ hagree
  rw [Measure.map_smul]
  exact OTSelector.Probability.normalized_seed_coordinate_law_of_atlas_haar
    (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj j e
    hK hsub hc0 hctop hprop himage

/-- **The three cell law inputs of an atlas cell from its label product law.**

If the normalized label cell law of an atlas window pushes forward under the
atlas mark map to the product of the uniform cube law and the mark law `α`, then
the normalized *physical* cell law has the uniform cube-coordinate law, the mark
law `α`, and independence of the cube coordinate and the mark. -/
theorem measured_atlas_cell_law_inputs_of_product_law
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (a : M → Z) {K : Set Z} (hK : MeasurableSet K) {q : ℕ}
    {Am : Type*} [MeasurableSpace Am]
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → Am) (hlabelS : Measurable labelS)
    (coordZ : Z → Fin q → ℝ) (hcoordZ : Measurable coordZ)
    (markZ : Z → Am) (hmarkZ : Measurable markZ) (α : Measure Am) [IsProbabilityMeasure α]
    (hu' : Measurable a) (η : Measure M) [IsFiniteMeasure η]
    (lambda : Measure Z) [IsFiniteMeasure lambda] (hηa : η.map a = lambda)
    (hprod : ((lambda K)⁻¹ • lambda.restrict K).map (fun z => (coordZ z, markZ z)) =
      (OTSelector.Probability.cubeMeasure (Fin q) 1).prod α)
    (hagreeC : coordS =ᵐ[η.restrict (a ⁻¹' K)] fun x => coordZ (a x))
    (hagreeM : labelS =ᵐ[η.restrict (a ⁻¹' K)] fun x => markZ (a x)) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map coordS =
        OTSelector.Probability.cubeMeasure (Fin q) 1 ∧
      ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map labelS = α ∧
      IndepFun coordS labelS ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) :=
  cell_law_inputs_of_label_product_law a hu' η lambda hηa hK coordS hcoordS labelS
    hlabelS coordZ hcoordZ markZ hmarkZ α hprod hagreeC hagreeM


/-! ## The canonical tile data inputs of the measured atlas -/

/-- **Exact cell masses and cube-coordinate laws of the canonical tile data.**

This is the packaged form of the two population inputs that the upper pressure
localization needs for *both* colours, for the canonical tile data built from
the actual measured atlas:

* the family of tiles is a measurable indexing `cellZ` of the common label
  space, so the physical cells `cellS = cellZ ∘ a` have exactly equal mass in the
  two colours, equal to the `ofReal` of the tile weight (the label mass of the cell);
* every tile carries an atlas window `j c`, a normalized seed basis `e c`, a
  uniform population density on its window piece, and the unit cube as its
  retained seed-label image; then the normalized physical cell law of the
  global atlas cube coordinate `coordS` is the uniform cube law, in both
  colours.

The remaining upper-localization inputs (the mark laws `α`, `β` and the
independence of cube coordinate and mark) are not produced by the measured
atlas: its joint law of seed label and clock is a composition product with a
conditional clock kernel.  They are supplied by
`cell_mark_law_of_label_law` and `cell_indep_of_label_indep` once the mark law
and independence of a cell are known, and remain explicit hypotheses of the
upper localization. -/
theorem measured_atlas_canonical_tile_mass_and_cube_inputs
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (a : M → (ℚ → M)) (ha : Measurable a) (lambda : Measure (ℚ → M))
    [IsFiniteMeasure lambda] (hμa : (μ : Measure M).map a = lambda)
    (hνa : (ν : Measure M).map a = lambda)
    (P : ℕ → F.CalibratedSeedWindow u)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, SigmaFinite (κ j)]
    (hu : let _instTileInputsMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {q : ℕ} (j : ι → ℕ) [∀ c, IsAddHaarMeasure (κ (j c))]
    (e : ∀ c, (P (j c)).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (cellZ : (ℚ → M) → ι) (hcellZ : Measurable cellZ)
    (hpiece : ∀ c, cellZ ⁻¹' {c} ⊆ populationSeedRootPiece P a κ lambda (j c))
    (cc : ι → ℝ≥0∞) (hc0 : ∀ c, cc c ≠ 0) (hctop : ∀ c, cc c ≠ ⊤)
    (hprop : ∀ c, lambda.restrict (populationSeedRootPiece P a κ lambda (j c)) =
      cc c • populationSeedLabelReference (P (j c)).seed a (κ (j c)))
    (himage : ∀ c, (e c) '' (populationSeedRootLabelValue (P (j c)).seed a ''
      (cellZ ⁻¹' {c})) = OTSelector.Probability.seedUnitCube q)
    (coordS : M → Fin q → ℝ)
    (hagree : ∀ c, coordS =ᵐ[(μ : Measure M).restrict (a ⁻¹' (cellZ ⁻¹' {c}))]
      fun x => atlasSeedCoord (P (j c)).seed (e c) a (a x))
    (hagreeT : ∀ c, coordS =ᵐ[(ν : Measure M).restrict (a ⁻¹' (cellZ ⁻¹' {c}))]
      fun x => atlasSeedCoord (P (j c)).seed (e c) a (a x)) :
    (∀ c, (μ : Measure M) ((fun x => cellZ (a x)) ⁻¹' {c}) =
        ENNReal.ofReal ((lambda (cellZ ⁻¹' {c})).toReal)) ∧
      (∀ c, (ν : Measure M) ((fun x => cellZ (a x)) ⁻¹' {c}) =
        ENNReal.ofReal ((lambda (cellZ ⁻¹' {c})).toReal)) ∧
      (∀ c, (((μ : Measure M) (a ⁻¹' (cellZ ⁻¹' {c})))⁻¹ •
          (μ : Measure M).restrict (a ⁻¹' (cellZ ⁻¹' {c}))).map coordS =
        OTSelector.Probability.cubeMeasure (Fin q) 1) ∧
      (∀ c, (((ν : Measure M) (a ⁻¹' (cellZ ⁻¹' {c})))⁻¹ •
          (ν : Measure M).restrict (a ⁻¹' (cellZ ⁻¹' {c}))).map coordS =
        OTSelector.Probability.cubeMeasure (Fin q) 1) := by
  refine ⟨fun c => cell_mass_eq_ofReal_label_mass a ha hμa cellZ hcellZ c,
    fun c => cell_mass_eq_ofReal_label_mass a ha hνa cellZ hcellZ c, ?_, ?_⟩
  · intro c
    exact measured_atlas_cell_cube_law P a κ lambda hF hcomplete hu ha hinj (j c)
      (e c) (hcellZ (measurableSet_singleton c)) (hpiece c) (hc0 c) (hctop c)
      (hprop c) (himage c) (μ : Measure M) hμa coordS (hagree c)
  · intro c
    exact measured_atlas_cell_cube_law P a κ lambda hF hcomplete hu ha hinj (j c)
      (e c) (hcellZ (measurableSet_singleton c)) (hpiece c) (hc0 c) (hctop c)
      (hprop c) (himage c) (ν : Measure M) hνa coordS (hagreeT c)

/-- **The measured atlas gives exactly balanced cell masses.**  Every measurable
indexing of the common label space produced by the measured atlas has, in the two
original populations, identical cell masses equal to the `ofReal` of the label mass
(hence of the tile weight). -/
theorem exists_measured_atlas_exact_cell_masses
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M,
      ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
        (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
        (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (cellZ : (ℚ → M) → ι) (hcellZ : Measurable cellZ) :
    ∃ (a : M → (ℚ → M)) (lambda : Measure (ℚ → M)),
      Measurable a ∧ (μ : Measure M).map a = lambda ∧ (ν : Measure M).map a = lambda ∧
      ∀ c, (μ : Measure M) ((fun x => cellZ (a x)) ⁻¹' {c}) =
          ENNReal.ofReal ((lambda (cellZ ⁻¹' {c})).toReal) ∧
        (ν : Measure M) ((fun x => cellZ (a x)) ⁻¹' {c}) =
          ENNReal.ofReal ((lambda (cellZ ⁻¹' {c})).toReal) := by
  obtain ⟨a, ha, hbalance⟩ := exists_measured_atlas_common_label_law (F := F)
    hF hcomplete m (μ : Measure M) (ν : Measure M) hμchart hνchart hA hB hAB hμ hν
  refine ⟨a, (μ : Measure M).map a, ha, rfl, hbalance.symm, ?_⟩
  intro c
  have hνa : (ν : Measure M).map a = (μ : Measure M).map a := hbalance.symm
  exact ⟨cell_mass_eq_ofReal_label_mass a ha rfl cellZ hcellZ c,
    cell_mass_eq_ofReal_label_mass a ha hνa cellZ hcellZ c⟩

end OTSelector.Reconstruction
