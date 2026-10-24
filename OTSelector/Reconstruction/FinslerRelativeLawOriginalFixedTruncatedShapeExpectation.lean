import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedTruncatedHaarShapePrefix
import OTSelector.Reconstruction.FinslerRelativeLawActualTruncatedHaarShapePrefix
import OTSelector.Reconstruction.FinslerRelativeLawOriginalSeedShapeExpectation
import OTSelector.Reconstruction.FinslerRelativeLawActualTruncatedClassObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedHaarShapePrefix
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation

/-! Exact finite class/Haar prefix laws on the actual original marked sample.
The physical inverse, original weighted clock-bin split, class normalization,
and binomial count mass are all discharged from the original population data. -/

open Set Function MeasureTheory ProbabilityTheory BoxIntegral Manifold OTSelector.Geometry
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


/-- Actual original population data supply the exact integrable canonical cell
mean on the same residual experiment, including every null microcell. -/
theorem PopulationLocalPressureCore.actual_original_truncated_shape_mean_of_classifier
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {G : Set (ℚ → M)} (hG : MeasurableSet G) (hLG : L ⊆ G)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (classify : ℝ → Fin Q.count) (hm : Measurable classify)
    (hclass : ∀ j x, x ∈ Q.cell j → classify x = j)
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
    (n : ℕ) [NeZero n]
    (index : Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℤ)
    (hcellbox : ∀ z ∈ L, (Module.finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL (populationSeedRootLabelValue
      (P (D.haar.continuous.coefficient i).seedIndex).seed a z) ∈ (unitPartition.box n index : Set _))
    (hboxProbability : ((κ (D.haar.continuous.coefficient i).seedIndex)
      ((Module.finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL ⁻¹' (unitPartition.box n index : Set _)) * (clockClassPairMeasure P₀) univ).toNNReal ≤ 1) :
    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let _instClass := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let p : unitInterval := ⟨((κ C.seedIndex) (e ⁻¹' (unitPartition.box n index : Set _)) *
      (clockClassPairMeasure P₀) univ).toNNReal, NNReal.coe_nonneg _, (by exact_mod_cast hboxProbability)⟩
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    ∀ (source target : Fin Q.count → ℝ),
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) →
      ∀ (N : ℕ) (tilt : ℝ),
      let extra := fun (_ : Unit) (cloud : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
        C.clockClassAllowed Q (classify (u (cloud.1 jk.1).1)) (classify (u (cloud.2 jk.2).1)))
      let score := fun (_ : Unit) (cloud : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) j k ↦
        (N : ℝ) ^ (2 / (q : ℝ)) * C.clockClassKinetic Q z₀
          (classify (u (cloud.1 j).1)) (classify (u (cloud.2 k).1))
          (e (R (a (cloud.2 k).1) - R (a (cloud.1 j).1))) +
          tilt * C.clockClassProbe Q z₀ hz₀ f (classify (u (cloud.1 j).1)) (classify (u (cloud.2 k).1))
      let value := fun sample ↦ (originalRetainedCellOptimizer a (fun _ : Unit ↦ L)
        extra score () sample).cost (score () sample)
      Integrable value (Refined.markedLaw N) ∧
        (∫ sample, value sample ∂Refined.markedLaw N) =
          affineClassBinomialShapeExpectation source target α β N p (n : ℝ≥0)⁻¹
            (fun l ↦ (index l : ℝ) / n) (originalMicrocellShape e n index (R '' L))
            (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  letI := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
  let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
  let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
  letI : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI : Nonempty (Fin Q.count) := nonempty_of_isProbabilityMeasure α
  let p : unitInterval := ⟨((κ C.seedIndex) (e ⁻¹' (unitPartition.box n index : Set _)) *
    (clockClassPairMeasure P₀) univ).toNNReal, NNReal.coe_nonneg _, (by exact_mod_cast hboxProbability)⟩
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  let Refined := Cst.refineSubplan ξG hξG
  obtain ⟨source₀, target₀, rankBins, bound, hcode₀, hbound, hcompare⟩ :=
    C.exists_clockClass_affine_binomial_shape_comparison Q z₀ hz₀ f P₀ hP₀ hmass hq
  have hlaw :=
    D.actual_original_truncated_haar_shape_law_of_classifier hF hcomplete hu ha hinj i hL hsub
      hG hLG Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf hPf hresidual hrow hcol
      cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv hlabel0 hlabel1
      πWhole ξ hπWhole hsplit Cst e n index hcellbox hboxProbability
  have hs : MeasurableSet (R '' L) := D.haar.measurable_cell_label_image hcomplete i hL hsub
  have hside : 0 < (n : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  have hshape : MeasurableSet (originalMicrocellShape e n index (R '' L)) :=
    measurableSet_affineHaarCubeCoord_image e (fun l ↦ (index l : ℝ) / n) hside
      (hs.inter (measurableSet_affineHaarCube e _ _))
  have hroot : Measurable (fun x : M ↦ R (a x)) :=
    (measurable_populationSeedRootLabelValue (P C.seedIndex).seed hF hcomplete hu ha hinj).comp ha
  have hmark : Measurable (fun x : M ↦ classify (u x)) := hm.comp hu.continuous.measurable
  dsimp only
  intro source target hcode N tilt
  have Ishape₀ := (hcompare N p 1 (n : ℝ≥0)⁻¹ (by norm_num)
    (fun l ↦ (index l : ℝ) / n) (originalMicrocellShape e n index (R '' L)) hshape tilt).1
  have hvalue : (fun d : BlockData ((Fin q → ℝ) × Fin Q.count) × BlockData ((Fin q → ℝ) × Fin Q.count) ↦
      unclampedBlockLegalTilted q source target N (C.clockClassKinetic Q z₀)
        (C.clockClassProbe Q z₀ hz₀ f) tilt
        (mapBlockData (affineMarkedPoint (fun l ↦ (index l : ℝ) / n) ((n : ℝ≥0)⁻¹)) d.1)
        (mapBlockData (affineMarkedPoint (fun l ↦ (index l : ℝ) / n) ((n : ℝ≥0)⁻¹)) d.2)) =
      (fun d : BlockData ((Fin q → ℝ) × Fin Q.count) × BlockData ((Fin q → ℝ) × Fin Q.count) ↦
      unclampedBlockLegalTilted q source₀ target₀ N (C.clockClassKinetic Q z₀)
        (C.clockClassProbe Q z₀ hz₀ f) tilt
        (mapBlockData (affineMarkedPoint (fun l ↦ (index l : ℝ) / n) ((n : ℝ≥0)⁻¹)) d.1)
        (mapBlockData (affineMarkedPoint (fun l ↦ (index l : ℝ) / n) ((n : ℝ≥0)⁻¹)) d.2)) := by
    funext d
    exact unclampedBlockLegalTilted_eq_of_clock_codes (C.clockClassAllowed Q) source source₀
      target target₀ hcode hcode₀ N (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt _ _
  have result := Cst.original_retained_seed_shape_cost_integral ξG hξG N a L (ha hL)
    (fun x : M ↦ R (a x)) hroot e (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) hmark hmark
    (C.clockClassAllowed Q) source target hcode (measurable_of_countable source) (measurable_of_countable target)
    (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt
    (C.measurable_clockClassKinetic Q z₀) (C.measurable_clockClassProbe Q z₀ hz₀ f)
    α β p (fun l ↦ (index l : ℝ) / n) (n : ℝ≥0)⁻¹ hside
    (originalMicrocellShape e n index (R '' L)) (hlaw N)
  exact ⟨result.1.mpr (by
    simp only [NNReal.coe_inv]
    rw [hvalue]
    simpa only [NNReal.coe_inv, α, β, ProbabilityMeasure.toMeasure_map, clockClassJointProbability, ProbabilityMeasure.coe_mk, q] using Ishape₀), result.2⟩

end OTSelector.Reconstruction
