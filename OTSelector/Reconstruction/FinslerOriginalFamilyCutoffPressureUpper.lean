import OTSelector.Reconstruction.FinslerOriginalFamilyLimitingPressureUpper

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

/-- One deterministic global microscopic cutoff is constructed internally
from the actual original family. Its total ORIGINAL discarded label mass is
arbitrarily small and its SAME original model mean has the true limiting
pressure upper. No global cutoff, local trace or mass-control callback remains. -/
theorem PopulationLocalPressureCore.exists_original_family_cutoff_pressure_upper
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
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
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j, ∑ k, (Pf c z j k + residual c z j k) =
      (condDistrib u a η₀ z).real ((Q c).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ k, ∑ j, (Pf c z j k + residual c z j k) =
      (condDistrib u a η₁ z).real ((Q c).cell k))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (hKc : ∀ c, K c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) ((Q c).cell j) ((Q c).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) ((Q c).cell k) ((Q c).measurable_cell k) (fallbackT c k)))
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
    (f : M × M →ᵇ ℝ) (hdim : 6 ≤ Module.finrank ℝ E) :
    let Seed := fun (c : Cells) ↦ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
    let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
    let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
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
    ∀ (tilt budget tolerance : ℝ), 0 < budget → 0 < tolerance →
    ∃ (cutoff : ℕ → Cells → Set (ℚ → M))
      (hcutoff : ∀ N c, MeasurableSet (cutoff N c)),
      (∀ N, (∑ c, lambda.real (cell c \ cutoff N c)) ≤ budget) ∧
      let G := fun N ↦ ⋃ c, cell c ∩ cutoff N c
      let hG := fun N ↦ MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff N c)
      let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
      let hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
        rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
      let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
      let original := fun N ↦ D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1) (n := N)
        coreIndex Q reference classify cell f tilt (T := T)
      ∀ᶠ N in atTop,
        (∫ sample, original N sample ∂(Refined N).markedLaw N) / N ≤
          (∑ c, volume.real ((coord c) '' cell c) * limit c tilt) + tolerance := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let Seed := fun (c : Cells) ↦ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
  let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
  let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
  obtain ⟨cHaar,hcHaar,hmap,limit,hlimit,hupper⟩ := D.exists_original_family_limiting_pressure_upper
    hF hcomplete hu ha hinj coreIndex cell hcell hsub hdisj Q reference classify hm hclass
    fallbackS fallbackT P₀ hP₀ hmass hzero Pf residual hmPf hPf hresidual hrow hcol K hKc Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst f hdim
  refine ⟨cHaar,hcHaar,hmap,limit,hlimit,?_⟩
  intro tilt budget tolerance hbudget htolerance
  let ε := fun _ : Cells ↦ budget / ((Fintype.card Cells : ℝ) + 1)
  have hε (c : Cells) : 0 < ε c := div_pos hbudget (by positivity)
  obtain ⟨scale,hscale,indices,hloss,hmissing,hadded,hmean⟩ :=
    hupper tilt ε hε tolerance htolerance
  let cutoff := fun N c ↦ (coord c) ⁻¹' (⋃ ν ∈ indices c N,
    (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder (q c) (scale c) N) ν : Set _))
  have hmcoord (c : Cells) : Measurable (coord c) :=
    ((Module.finBasis ℝ (Seed c).covector.ker).equivFunL.continuous.measurable).comp
      (measurable_populationSeedRootLabelValue _ hF hcomplete hu ha hinj)
  have hcutoff (N : ℕ) (c : Cells) : MeasurableSet (cutoff N c) :=
    (MeasurableSet.iUnion fun ν ↦ MeasurableSet.iUnion fun _ ↦
      (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder (q c) (scale c) N) ν).measurableSet_coe).preimage
        (hmcoord c)
  refine ⟨cutoff,hcutoff,?_,?_⟩
  · intro N
    have hterm (c : Cells) : lambda.real (cell c \ cutoff N c) ≤ ε c := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hloss c N).le
      simpa only [measureReal_def, ENNReal.toReal_ofReal (hε c).le] using hh
    calc
      _ ≤ ∑ c, ε c := Finset.sum_le_sum (fun c _ ↦ hterm c)
      _ = (Fintype.card Cells : ℝ) * (budget / ((Fintype.card Cells : ℝ) + 1)) := by
        simp only [ε,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ ((Fintype.card Cells : ℝ) + 1) * (budget / ((Fintype.card Cells : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = budget := by field_simp
  · let G := fun N ↦ ⋃ c, cell c ∩ cutoff N c
    have hG : ∀ N, MeasurableSet (G N) := fun N ↦
      MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff N c)
    have htrace (c : Cells) (N : ℕ) : cell c ∩ G N = cell c ∩ cutoff N c :=
      original_cellwise_cutoff_trace cell (cutoff N) hdisj c
    exact (hmean G hG htrace).2

end OTSelector.Reconstruction
