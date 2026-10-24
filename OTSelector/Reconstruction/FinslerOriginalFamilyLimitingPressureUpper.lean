import OTSelector.Reconstruction.FinslerOriginalFamilyMeanPressureUpper
import OTSelector.Reconstruction.FinslerOriginalPressureSideChoice

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

/-- All fixed microscopic sides and their legal repair errors are eliminated
from the original finite-family mean upper bound. One true density-weighted
pressure limit is produced for each original coefficient cell. Arbitrarily
small original label losses are retained before any empirical sample is drawn. -/
theorem PopulationLocalPressureCore.exists_original_family_limiting_pressure_upper
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
    ∀ (tilt : ℝ) (ε : Cells → ℝ), (∀ c, 0 < ε c) → ∀ ζ : ℝ, 0 < ζ →
    ∃ (scale : Cells → ℝ), (∀ c, 0 < scale c) ∧
    ∃ indices : ∀ c, ℕ → Finset (Fin (q c) → ℤ),
      (∀ c N, lambda (cell c \ (coord c) ⁻¹' (⋃ ν ∈ indices c N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder (q c) (scale c) N) ν : Set _))) <
          ENNReal.ofReal (ε c)) ∧
      (∀ c N, volume (((coord c) '' cell c) \ (⋃ ν ∈ indices c N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder (q c) (scale c) N) ν : Set _))) <
          ENNReal.ofReal (ε c)) ∧
      (∀ c, Tendsto (fun N ↦ volume ((⋃ ν ∈ indices c N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder (q c) (scale c) N) ν : Set _)) \ ((coord c) '' cell c)))
        atTop (𝓝 0)) ∧
    ∀ (G : ℕ → Set (ℚ → M)) (hG : ∀ N, MeasurableSet (G N)),
      (∀ c N, cell c ∩ G N = cell c ∩ (coord c) ⁻¹' (⋃ ν ∈ indices c N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder (q c) (scale c) N) ν : Set _))) →
      let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
      let hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
        rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
      let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
      let original := fun N ↦ D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1) (n := N)
        coreIndex Q reference classify cell f tilt (T := T)
      (∀ᶠ N in atTop, Integrable (original N) ((Refined N).markedLaw N)) ∧
      ∀ᶠ N in atTop,
        (∫ sample, original N sample ∂(Refined N).markedLaw N) / N ≤
          (∑ c, volume.real ((coord c) '' cell c) * limit c tilt) + ζ := by
  classical
  let Seed := fun (c : Cells) ↦ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
  let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
  let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
  have hq (c : Cells) : 4 < q c := by
    have h := D.original_seed_label_finrank (coreIndex c)
    change q c = Module.finrank ℝ E - 1 at h
    omega
  obtain ⟨R,B,cHaar,hR,hB,hcHaar,hmap,hupper⟩ := D.exists_original_family_mean_pressure_upper
    hF hcomplete hu ha hinj coreIndex cell hcell hsub hdisj Q reference classify hm hclass
    fallbackS fallbackT P₀ hP₀ hmass hzero Pf residual hmPf hPf hresidual hrow hcol K hKc Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst f hdim
  let density := fun c ↦ cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
  have hdensity (c : Cells) : 0 < density c := by
    apply mul_pos (hcHaar c)
    apply ENNReal.toNNReal_pos
    · have hr : 0 < (clockClassPairMeasure (P₀ c)).real univ := by
        rw [clockClassPairMeasure_real_univ (P₀ c) (hP₀ c)]
        exact hmass c
      exact ne_of_gt ((ENNReal.toReal_pos_iff.mp hr).1)
    · exact measure_ne_top _ _
  have hpressure (c : Cells) :=
    (D.haar.continuous.coefficient (coreIndex c)).exists_physical_density_clockClassPressure_limit
      (Q c) (reference c).val (reference c).property f (P₀ c) (hP₀ c) (hzero c) (hmass c)
      (density c) (hdensity c) (hq c)
  choose p hp hconc hlip using hpressure
  let limit := fun c tilt ↦ (density c : ℝ) * p c tilt
  let rate := fun (c : Cells) (L : ℝ) ↦
    let C := D.haar.continuous.coefficient (coreIndex c)
    let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
    let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
    let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    finiteClassLegalPressure (q c) (C.clockClassAllowed (Q c)) α β
      (density c * Real.toNNReal (L ^ (q c))) (C.densityClockClassKinetic (Q c) (reference c).val (density c))
      (C.clockClassProbe (Q c) (reference c).val (reference c).property f)
  have hrate (c : Cells) (tilt : ℝ) : Tendsto (fun L : ℝ ↦ rate c L tilt / L ^ (q c))
      atTop (𝓝 (limit c tilt)) := by
    simpa only [rate,limit,ProbabilityMeasure.toMeasure_map,clockClassJointProbability,
      ProbabilityMeasure.coe_mk] using hp c tilt
  refine ⟨cHaar,hcHaar,hmap,limit,hrate,?_⟩
  intro tilt ε hε ζ hζ
  let Fbound := fun (c : Cells) (L : ℝ) ↦ volume.real ((coord c) '' cell c) * (rate c L tilt / L ^ (q c)) +
    activeGridRepairError (q c) (legalGridRepairConstant (q c) ((Q c).count + 1) ((Q c).count * (Q c).count))
      (B c) ‖f‖ tilt 1 ((L / (2 * (R c : ℝ))) ^ (q c))
  let target := fun c ↦ volume.real ((coord c) '' cell c) * limit c tilt
  have hFbound (c : Cells) : Tendsto (Fbound c) atTop (𝓝 (target c)) := by
    simpa only [Fbound,target,add_zero] using
      ((hrate c tilt).const_mul (volume.real ((coord c) '' cell c))).add
        (tendsto_original_macro_grid_repair_microscopic_side (hq c) (hR c)
          (legalGridRepairConstant (q c) ((Q c).count + 1) ((Q c).count * (Q c).count)) (B c) ‖f‖ tilt)
  obtain ⟨scale,accuracy,hscale,haccuracy,haccuracyLe,hsum⟩ :=
    exists_finite_family_pressure_sides_and_accuracy Fbound (fun c L ↦ rate c L tilt / L ^ (q c))
      target ε hFbound hε (half_pos hζ)
  obtain ⟨indices,hloss,hmissing,hadded,hmean⟩ := hupper scale accuracy hscale haccuracy
  refine ⟨scale,hscale,indices,?_,?_,hadded,?_⟩
  · intro c N
    exact (hloss c N).trans_le (ENNReal.ofReal_le_ofReal (haccuracyLe c))
  · intro c N
    exact (hmissing c N).trans_le (ENNReal.ofReal_le_ofReal (haccuracyLe c))
  intro G hG htrace
  have h := hmean G hG htrace tilt
  refine ⟨h.1,?_⟩
  filter_upwards [h.2 (ζ / 2) (half_pos hζ)] with N hN
  have hrateEq (c : Cells) :
      let C := D.haar.continuous.coefficient (coreIndex c)
      let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
      let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
      let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
      let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      finiteClassLegalPressure (q c) (C.clockClassAllowed (Q c)) α β
        (density c * ⟨scale c ^ (q c), pow_nonneg (hscale c).le _⟩)
        (C.densityClockClassKinetic (Q c) (reference c).val (density c))
        (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt / scale c ^ (q c) =
        rate c (scale c) tilt / scale c ^ (q c) := by
    dsimp only [rate]
    rw [Real.toNNReal_of_nonneg (pow_nonneg (hscale c).le _)]
    rfl
  have hsum' := hsum
  have heq : (Finset.univ.sum (fun (c : Cells) ↦ Fbound c (scale c) + accuracy c * |rate c (scale c) tilt / scale c ^ (q c)|)) =
      ∑ c,
        let C := D.haar.continuous.coefficient (coreIndex c)
        let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
        let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
        let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
        let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
        let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
        let pp := finiteClassLegalPressure (q c) (C.clockClassAllowed (Q c)) α β
          (density c * ⟨scale c ^ (q c), pow_nonneg (hscale c).le _⟩)
          (C.densityClockClassKinetic (Q c) (reference c).val (density c))
          (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt / scale c ^ (q c)
        volume.real ((coord c) '' cell c) * pp + accuracy c * |pp| +
          activeGridRepairError (q c) (legalGridRepairConstant (q c) ((Q c).count + 1) ((Q c).count * (Q c).count))
            (B c) ‖f‖ tilt 1 ((scale c / (2 * (R c : ℝ))) ^ (q c)) := by
    apply Finset.sum_congr rfl
    intro c _
    dsimp only
    rw [hrateEq c]
    dsimp only [Fbound]
    ring
  rw [heq] at hsum'
  have hfinal := hN.trans (add_le_add hsum' (le_refl (ζ / 2)))
  simpa only [target] using (show _ ≤ (∑ c, target c) + ζ by linarith)

end OTSelector.Reconstruction
