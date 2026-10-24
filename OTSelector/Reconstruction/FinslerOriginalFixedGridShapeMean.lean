import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedMicrocellShapeExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalHaarGridProbability

/-! The fixed original classifier has exact microscopic binomial shape means.
One actual Haar factor works before every shape, grid and deterministic cutoff. -/
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


/-- The same actual original microcell cost sum has the literal homogeneous
grid probability eventually, with one original Haar factor before all scales
and deterministic spatial selections. All positivity and box-law premises
are discharged internally, including every null retained microcell. -/
theorem PopulationLocalPressureCore.exists_actual_original_grid_shape_means_of_classifier
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
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
 :
    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let _instClass := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    ∃ cHaar : ℝ≥0, 0 < cHaar ∧
      (κ C.seedIndex).map e = (cHaar : ℝ≥0∞) • (volume : Measure (Fin q → ℝ)) ∧
      ∀ (scale : ℝ), 0 < scale →
      ∀ (indices : ℕ → Finset (Fin q → ℤ)) (G : ℕ → Set (ℚ → M)) (hG : ∀ N, MeasurableSet (G N)),
      (∀ N, ∀ ν ∈ indices N, ∀ z ∈ L,
        e (R z) ∈ (unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set _) → z ∈ G N) →
      ∀ᶠ N : ℕ in atTop,
      let n := positiveMicroscopicGridOrder q scale N
      let ξG := restrictOriginalRetainedResidual χ ξ a (G N)
      let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
      let Refined := Cst.refineSubplan ξG hξG
      let microcell := fun ν : {ν // ν ∈ indices N} ↦
        L ∩ (fun z ↦ e (R z)) ⁻¹' (unitPartition.box n ν.val : Set _)
      let p := positiveMicroscopicCubeProbability q (cHaar * (clockClassPairMeasure P₀ univ).toNNReal) scale N
        ∀ (source target : Fin Q.count → ℝ),
        (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) → ∀ tilt : ℝ,
        let value := fun sample ↦ ∑ ν : {ν // ν ∈ indices N},
          originalRetainedSeedClassCost a (microcell ν) (fun x ↦ R (a x)) e.toLinearMap
            (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
            ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt sample
        Integrable value (Refined.markedLaw N) ∧
          (∫ sample, value sample ∂Refined.markedLaw N) =
            ∑ ν : {ν // ν ∈ indices N}, affineClassBinomialShapeExpectation source target α β N p
              (n : ℝ≥0)⁻¹ (fun l ↦ (ν.val l : ℝ) / n) (originalMicrocellShape e n ν.val (R '' L))
              (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt := by
  classical
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
  obtain ⟨cHaar, hcHaar, hmap, hprob⟩ := exists_original_haar_grid_box_probabilities (κ C.seedIndex) e hq
  refine ⟨cHaar, hcHaar, hmap, ?_⟩
  intro scale hscale indices G hG hcover
  filter_upwards [hprob (clockClassPairMeasure P₀ univ) scale hscale] with N hN
  have hmean := D.actual_original_microcell_shape_means_of_classifier
    hF hcomplete hu ha hinj i hL hsub (hG N) Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf hPf
    hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv hlabel0 hlabel1
    πWhole ξ hπWhole hsplit Cst z₀ hz₀ f hq (positiveMicroscopicGridOrder q scale N) (indices N)
    (hcover N) (fun ν _ ↦ (hN ν).1)
  dsimp only
  intro source target hcode tilt
  have h := hmean source target hcode N tilt
  dsimp only at h ⊢
  refine ⟨h.1, h.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro ν _
  congr 1
  exact Subtype.ext (hN ν.val).2

end OTSelector.Reconstruction
