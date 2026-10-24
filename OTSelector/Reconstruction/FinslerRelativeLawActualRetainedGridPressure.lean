import OTSelector.Reconstruction.FinslerRelativeLawActualGridShapeExpectation
import OTSelector.Reconstruction.FinslerRelativeLawActualCellShapeMean

/-! Exact finite class/Haar prefix laws on the actual original marked sample.
The physical inverse, original weighted clock-bin split, class normalization,
and binomial count mass are all discharged from the original population data. -/

open Set Function MeasureTheory ProbabilityTheory BoxIntegral Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical unitInterval BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- Deterministic witnesses to an eventual dependent existence statement can
be chosen at every index without changing its eventual conclusions. -/
theorem exists_dependent_choice_of_eventually_exists
    {Index : Type*} {l : Filter Index} {Y : Index → Type*} [∀ i, Nonempty (Y i)]
    {R : ∀ i, Y i → Prop} (h : ∀ᶠ i in l, ∃ y, R i y) :
    ∃ f : ∀ i, Y i, ∀ᶠ i in l, R i (f i) := by
  classical
  refine ⟨fun i ↦ if hi : ∃ y, R i y then hi.choose else Classical.choice inferInstance, ?_⟩
  filter_upwards [h] with i hi
  simpa only [dite_eq_left hi] using hi.choose_spec

/-- Actual original retained canonical grid means converge uniformly on
compact tilt intervals to their true filling-volume legal pressure. The
original microscopic cover, label loss, Haar density, finite binomial shape
laws and integrability are all produced internally; deterministic global
retention may preserve other original coefficient cells. -/
theorem PopulationLocalPressureCore.exists_actual_original_retained_grid_pressure_error
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (fallbackS fallbackT : Fin Q.count → ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ) (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (Pf residual : (ℚ → M) → Fin Q.count → Fin Q.count → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z)
    (hresidual : ∀ᵐ z ∂lambda.restrict L, ∀ j k, 0 ≤ residual z j k)
    (hrow : ∀ᵐ z ∂lambda.restrict L, ∀ j, ∑ k, (Pf z j k + residual z j k) =
      (condDistrib u a η₀ z).real (Q.cell j))
    (hcol : ∀ᵐ z ∂lambda.restrict L, ∀ k, ∑ j, (Pf z j k + residual z j k) =
      (condDistrib u a η₁ z).real (Q.cell k))
    {Cells : Type*} [Fintype Cells]
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (c : Cells) (hc : L ⊆ cell c)
    (hKc : K c = finiteClassPopulationKernel Pf
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Q.cell j) (Q.measurable_cell j) (fallbackS j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Q.cell k) (Q.measurable_cell k) (fallbackT k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x) (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (πWhole ξ : Measure (M × M)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {T : Type*} [Fintype T] {qAtlas : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T qAtlas cost)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    (z₀ : ℚ → M) (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ)
    (hq : 0 < Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
 :
    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let coord := atlasSeedCoord (P C.seedIndex).seed e a
    let _instClass := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    ∃ cHaar : ℝ≥0, 0 < cHaar ∧ ∃ source target : Fin Q.count → ℝ,
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧
      ∀ (scale : ℝ) (hscale : 0 < scale), ∀ (ε : ℝ≥0∞), 0 < ε →
      ∃ indices : ℕ → Finset (Fin q → ℤ),
        (∀ N, lambda (L \ coord ⁻¹' (⋃ ν ∈ indices N,
          (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ)))) < ε) ∧
        (∀ N, volume ((coord '' L) \ (⋃ ν ∈ indices N,
          (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ)))) < ε) ∧
        Tendsto (fun N ↦ volume ((⋃ ν ∈ indices N,
          (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ))) \ (coord '' L))) atTop (𝓝 0) ∧
      ∀ (G : ℕ → Set (ℚ → M)) (hG : ∀ N, MeasurableSet (G N)),
      (∀ N, ∀ ν ∈ indices N, ∀ z ∈ L,
        coord z ∈ (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set _) → z ∈ G N) →
      ∃ classify : ∀ N, {ν // ν ∈ indices N} → ℝ → Fin Q.count,
      let density := cHaar * (clockClassPairMeasure P₀ univ).toNNReal
      let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
      let hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
        rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
      let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
      let microcell := fun N (ν : {ν // ν ∈ indices N}) ↦
        L ∩ coord ⁻¹' (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν.val : Set _)
      let value := fun N tilt sample ↦ ∑ ν : {ν // ν ∈ indices N},
        originalRetainedSeedClassCost a (microcell N ν) (fun x ↦ R (a x)) e.toLinearMap
          (fun x ↦ classify N ν (u x)) (fun x ↦ classify N ν (u x)) (C.clockClassAllowed Q)
          ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt sample
      (∀ᶠ N : ℕ in atTop,
        (∀ ν, Measurable (classify N ν) ∧ ∀ j x, x ∈ Q.cell j → classify N ν x = j) ∧
        ∀ tilt : ℝ, Integrable (value N tilt) ((Refined N).markedLaw N)) ∧
      ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn
        (fun N tilt ↦ (∫ sample, value N tilt sample ∂(Refined N).markedLaw N) / N -
          volume.real (⋃ ν ∈ indices N,
            (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ))) *
          (finiteClassLegalPressure q (C.clockClassAllowed Q) α β
            (density * ⟨scale ^ q, pow_nonneg hscale.le q⟩)
            (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt / scale ^ q))
        (fun _ ↦ 0) atTop (Icc (-T) T) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let coord := atlasSeedCoord (P C.seedIndex).seed e a
  letI := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
  let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
  let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
  letI : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI : Nonempty (Fin Q.count) := nonempty_of_isProbabilityMeasure α
  obtain ⟨cHaar, hcHaar, hmean⟩ := D.exists_actual_original_grid_canonical_shape_means
    hF hcomplete hu ha hinj i hL hsub Q fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf hPf
    hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv hlabel0 hlabel1
    πWhole ξ hπWhole hsplit Cst z₀ hz₀ f hq
  let density := cHaar * (clockClassPairMeasure P₀ univ).toNNReal
  have hdensity : 0 < density := by
    apply mul_pos hcHaar
    apply ENNReal.toNNReal_pos
    · have hreal : 0 < (clockClassPairMeasure P₀).real univ := by
        rw [clockClassPairMeasure_real_univ P₀ hP₀]
        exact hmass
      exact ne_of_gt ((ENNReal.toReal_pos_iff.mp hreal).1)
    · exact measure_ne_top _ _
  obtain ⟨source, target, hcode, hshape⟩ :=
    D.exists_actual_cell_binomialShape_pressure_error hF hcomplete hu ha hinj i hL hsub Q z₀ hz₀ f P₀ hP₀ hmass hq e
  refine ⟨cHaar, hcHaar, source, target, hcode, ?_⟩
  intro scale hscale ε hε
  obtain ⟨indices, hloss, hmissing, hadded, hpressure⟩ := hshape density hdensity scale hscale ε hε
  refine ⟨indices, hloss, hmissing, hadded, ?_⟩
  intro G hG hcover
  obtain ⟨classify, hclassify⟩ := exists_dependent_choice_of_eventually_exists
    (hmean scale hscale indices G hG hcover)
  refine ⟨classify, ?_, ?_⟩
  · filter_upwards [hclassify] with N hN
    exact ⟨hN.1, fun tilt ↦ (hN.2 source target hcode tilt).1⟩
  intro T hT
  have hpressure' := hpressure T hT
  apply hpressure'.congr
  filter_upwards [hclassify] with N hN
  intro tilt _
  have h := (hN.2 source target hcode tilt).2
  dsimp only at h ⊢
  have hside : (⟨positiveMicroscopicGridSide q scale N, positiveMicroscopicGridSide_nonneg q scale N⟩ : ℝ≥0) =
      (positiveMicroscopicGridOrder q scale N : ℝ≥0)⁻¹ := by
    apply Subtype.ext
    rfl
  have hsum : (∑ ν ∈ indices N, affineClassBinomialShapeExpectation source target
      ((clockClassJointProbability P₀ hP₀ hmass).map measurable_fst.aemeasurable : Measure _)
      ((clockClassJointProbability P₀ hP₀ hmass).map measurable_snd.aemeasurable : Measure _)
      N (positiveMicroscopicCubeProbability q density scale N)
      ⟨positiveMicroscopicGridSide q scale N, positiveMicroscopicGridSide_nonneg q scale N⟩
      (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q scale N)
      (originalMicrocellShape (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
        (positiveMicroscopicGridOrder q scale N) ν (coord '' L))
      (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) =
      ∑ ν : {ν // ν ∈ indices N}, affineClassBinomialShapeExpectation source target α β
        N (positiveMicroscopicCubeProbability q density scale N)
        (positiveMicroscopicGridOrder q scale N : ℝ≥0)⁻¹
        (fun l ↦ (ν.val l : ℝ) / positiveMicroscopicGridOrder q scale N)
        (originalMicrocellShape e (positiveMicroscopicGridOrder q scale N) ν.val (R '' L))
        (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hside]
    have hcoords : coord '' L = e '' (R '' L) := by exact (image_image e R L).symm
    rw [hcoords, originalMicrocellShape_linear_image e]
    simp only [α, β, ProbabilityMeasure.toMeasure_map, clockClassJointProbability, ProbabilityMeasure.coe_mk]
  rw [hsum, ← h]
  rfl

end OTSelector.Reconstruction
