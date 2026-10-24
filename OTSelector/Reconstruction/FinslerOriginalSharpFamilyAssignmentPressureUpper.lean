import OTSelector.Reconstruction.FinslerOriginalFamilyCutoffPressureUpper
import OTSelector.Reconstruction.FinslerOriginalSharpPressureEnvelope

/-! A finite original coefficient family has its combined pressure upper
on the one unchanged original population and original iid cloud. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
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

/-- The true original full iid assignment has the limiting original-family
pressure upper. Actual Haar/class/binomial laws, microscopic filling, parent
repair, global cutoff and total discarded label control are produced internally.
The only surviving errors are the existing physical geometry/probe error and
one true base residual ξ; the original population and classifier stay fixed. -/
theorem PopulationLocalPressureCore.exists_original_sharp_family_assignment_pressure_upper
    (D : PopulationLocalPressureCore P a κ (η₀.map a) η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {Cells : Type*} [Fintype Cells]
    (coreIndex : Cells → Fin D.haar.continuous.count)
    [∀ c, (κ (D.haar.continuous.coefficient (coreIndex c)).seedIndex).IsAddHaarMeasure]
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots)
    (hdisj : Pairwise (Disjoint on cell))
    {range : Set ℝ} {width : ℝ} (Q : Cells → FiniteScalarBins range width)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (hm : ∀ c, Measurable (classify c))
    (hclass : ∀ c j x, x ∈ (Q c).cell j → classify c x = j)
    (fallbackS fallbackT : ∀ c, Fin (Q c).count → ℝ)
    (P₀ : ∀ c, Fin (Q c).count → Fin (Q c).count → ℝ)
    (hP₀ : ∀ c j k, 0 ≤ P₀ c j k) (hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k)
    (hzero : ∀ c j k, ¬(D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k → P₀ c j k = 0)
    (Pf residual : ∀ c, (ℚ → M) → Fin (Q c).count → Fin (Q c).count → ℝ)
    (hmPf : ∀ c j k, Measurable (fun z ↦ Pf c z j k))
    (hPf : ∀ c z, z ∈ cell c → ∀ j k, Pf c z j k = P₀ c j k / D.rootIntensity (coreIndex c) z)
    (hresidual : ∀ c, ∀ᵐ z ∂(η₀.map a).restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂(η₀.map a).restrict (cell c), ∀ j, ∑ k, (Pf c z j k + residual c z j k) =
      (condDistrib u a η₀ z).real ((Q c).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂(η₀.map a).restrict (cell c), ∀ k, ∑ j, (Pf c z j k + residual c z j k) =
      (condDistrib u a η₁ z).real ((Q c).cell k))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (hKc : ∀ c, K c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) ((Q c).cell j) ((Q c).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) ((Q c).cell k) ((Q c).measurable_cell k) (fallbackT c k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂(η₀.map a), Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x) (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel1 : η₁.map a = (η₀.map a))
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hχ : χ = ((((η₀.map a) ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)))
    (hπWhole : Vlasov.IsCoupling (χ + ξ) η₀ η₁)
    {T : Type*} [Fintype T]
    (Cst : PopulationTypedCostData (χ + ξ) η₀ η₁ T (Module.finrank ℝ E - 1)
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (f : M × M →ᵇ ℝ) (hdim : 6 ≤ Module.finrank ℝ E)
    (geometryError probeError : ℝ)
    (hsharp : D.originalWeightSharpExpectedBound coreIndex Q reference classify cell hcell f
      geometryError probeError χ ξ Cst ha) :
    let Seed := fun (c : Cells) ↦ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
    let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
    let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
    ∃ cHaar : Cells → ℝ≥0, (∀ c, 0 < cHaar c) ∧
    (∀ c, (κ (D.haar.continuous.coefficient (coreIndex c)).seedIndex).map
      (Module.finBasis ℝ (Seed c).covector.ker).equivFunL =
        (cHaar c : ℝ≥0∞) • (volume : Measure (Fin (q c) → ℝ))) ∧
    ∃ limit : Cells → ℝ → ℝ,
      (∀ c,
        let C := D.haar.continuous.coefficient (coreIndex c)
        let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
        let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
        let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
        let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
        let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
        let density := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
        ∀ tilt, Tendsto (fun L : ℝ ↦ finiteClassLegalPressure (q c) (C.clockClassAllowed (Q c)) α β
          (density * Real.toNNReal (L ^ (q c))) (C.densityClockClassKinetic (Q c) (reference c).val density)
          (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt / L ^ (q c))
          atTop (𝓝 (limit c tilt))) ∧
    ∀ tilt : ℝ,
      let iid := fun N ↦ (Measure.pi (fun _ : Fin N ↦ η₀)).prod (Measure.pi (fun _ : Fin N ↦ η₁))
      let assignment := fun N (sample : (Fin N → M) × (Fin N → M)) ↦ perturbedAssignmentValue
        (fun i j ↦ (N : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
          ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
          tilt * f (sample.1 i,sample.2 j)) 0 0
      let A := Cst.quadraticConstant * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
        (Fintype.card T : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
      let geometry := (3 * geometryError + 2 * geometryError ^ 2) *
          (A / (1 - (3 * geometryError + 2 * geometryError ^ 2)) + |tilt| * ‖f‖ + 1) +
        (|tilt| * (2 * probeError) + (3 * geometryError + 2 * geometryError ^ 2) * (|tilt| * ‖f‖))
      (∀ N, 0 < N → Integrable (assignment N) (iid N)) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ N in atTop,
        (∫ sample, assignment N sample ∂iid N) / N ≤
          (∑ c, volume.real ((coord c) '' cell c) * limit c tilt) + geometry +
            (A * (ξ univ).toReal ^ (1 - 2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
              2 * |tilt| * ‖f‖ * (ξ univ).toReal) + ζ := by
  classical
  subst χ
  let Seed := fun (c : Cells) ↦ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
  let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
  let χ := ((((η₀.map a) ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  obtain ⟨cHaar,hcHaar,hmap,limit,hlimit,hmodel⟩ := D.exists_original_family_cutoff_pressure_upper
    hF hcomplete hu ha hinj coreIndex cell hcell hsub hdisj Q reference classify hm hclass
    fallbackS fallbackT P₀ hP₀ hmass hzero Pf residual hmPf hPf hresidual hrow hcol K hKc Qglobal hwhole
    hb hη₀inv hη₁inv rfl hlabel1 (χ + ξ) ξ hπWhole rfl Cst f hdim
  refine ⟨cHaar,hcHaar,hmap,limit,hlimit,?_⟩
  exact D.original_sharp_assignment_upper_of_model_pressure coreIndex Q reference classify cell hcell f
    geometryError probeError χ ξ Cst ha (by omega) hsharp
    (fun tilt ↦ ∑ c, volume.real ((coord c) '' cell c) * limit c tilt) hmodel

end OTSelector.Reconstruction
