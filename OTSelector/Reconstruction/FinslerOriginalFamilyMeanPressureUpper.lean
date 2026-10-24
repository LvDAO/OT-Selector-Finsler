import OTSelector.Reconstruction.FinslerOriginalCellMeanPressureUpper
import OTSelector.Reconstruction.FinslerOriginalFamilyModelMean
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentMicrocellCutoff

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

/-- The same original population, classifier family and global retained
experiment satisfy the finite-family pressure upper after the sample limit.
The microscopic grids are fixed before sampling. Different original cells
may use their own chart and fixed microscopic side; no cellwise population
replacement or independent adaptive remainder is introduced. -/
theorem PopulationLocalPressureCore.exists_original_family_mean_pressure_upper
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
    let q := fun (c : Cells) ↦ Module.finrank ℝ (Seed c).covector.ker
    let coord := fun (c : Cells) ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    ∃ (R : Cells → ℕ) (B : Cells → ℝ) (cHaar : Cells → ℝ≥0),
      (∀ c, 0 < R c) ∧ (∀ c, 0 ≤ B c) ∧ (∀ c, 0 < cHaar c) ∧
      (∀ c, (κ (D.haar.continuous.coefficient (coreIndex c)).seedIndex).map
        (Module.finBasis ℝ (Seed c).covector.ker).equivFunL =
        (cHaar c : ℝ≥0∞) • (volume : Measure (Fin (q c) → ℝ))) ∧
    ∀ (scale ε : Cells → ℝ) (hscale : ∀ c, 0 < scale c) (hε : ∀ c, 0 < ε c),
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
    ∀ tilt : ℝ,
      let rate := fun (c : Cells) ↦
        let C := D.haar.continuous.coefficient (coreIndex c)
        let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
        let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
        let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
        let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
        let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
        let density := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
        finiteClassLegalPressure (q c) (C.clockClassAllowed (Q c)) α β
          (density * ⟨scale c ^ (q c), pow_nonneg (hscale c).le _⟩)
          (C.densityClockClassKinetic (Q c) (reference c).val density)
          (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt / scale c ^ (q c)
      let bound := fun (c : Cells) ↦ volume.real ((coord c) '' cell c) * rate c + ε c * |rate c| +
        activeGridRepairError (q c) (legalGridRepairConstant (q c) ((Q c).count + 1) ((Q c).count * (Q c).count))
          (B c) ‖f‖ tilt 1 ((scale c / (2 * (R c : ℝ))) ^ (q c))
      let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
      let hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
        rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
      let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
      let original := fun N ↦ D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1) (n := N)
        coreIndex Q reference classify cell f tilt (T := T)
      (∀ᶠ N in atTop, Integrable (original N) ((Refined N).markedLaw N)) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ N in atTop,
        (∫ sample, original N sample ∂(Refined N).markedLaw N) / N ≤
          (∑ c, bound c) + ζ := by
  classical
  let Seed := fun (c : Cells) ↦ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
  let q := fun (c : Cells) ↦ Module.finrank ℝ (Seed c).covector.ker
  let coord := fun (c : Cells) ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
  have hq (c : Cells) : 4 < q c := by
    have h := D.original_seed_label_finrank (coreIndex c)
    change q c = Module.finrank ℝ E - 1 at h
    omega
  have hfactory (c : Cells) := D.exists_original_cell_mean_pressure_upper
    hF hcomplete hu ha hinj (coreIndex c) (hcell c) (hsub c) (Q c) (classify c) (hm c) (hclass c)
    (fallbackS c) (fallbackT c) (P₀ c) (hP₀ c) (hmass c) (Pf c) (residual c) (hmPf c) (hPf c)
    (hresidual c) (hrow c) (hcol c) cell hcell hdisj K c (Subset.refl _) (hKc c) Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst (reference c) f (hzero c) (hq c)
  choose R B cHaar hR hB hcHaar hmap hupper using hfactory
  refine ⟨R,B,cHaar,hR,hB,hcHaar,hmap,?_⟩
  intro scale ε hscale hε
  choose indices hloss hmissing hadded hlocal using fun c ↦ hupper c (scale c) (hscale c) (ε c) (hε c)
  refine ⟨indices,hloss,hmissing,hadded,?_⟩
  intro G hG htrace tilt
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
  have hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
    rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
  let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
  let original := fun N ↦ D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1) (n := N)
    coreIndex Q reference classify cell f tilt (T := T)
  let value := fun c (N : ℕ) ↦
    let C := D.haar.continuous.coefficient (coreIndex c)
    let root := populationSeedRootLabelValue (Seed c) a
    let e := (Module.finBasis ℝ (Seed c).covector.ker).equivFunL
    originalRetainedSeedClassCost (T := T) (N := N) a (cell c) (fun x ↦ root (a x)) e.toLinearMap
      (fun x ↦ classify c (u x)) (fun x ↦ classify c (u x)) (C.clockClassAllowed (Q c))
      ((N : ℝ) ^ (2 / (q c : ℝ))) (C.clockClassKinetic (Q c) (reference c).val)
      (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt
  let rate := fun (c : Cells) ↦
    let C := D.haar.continuous.coefficient (coreIndex c)
    let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
    let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
    let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let density := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
    finiteClassLegalPressure (q c) (C.clockClassAllowed (Q c)) α β
      (density * ⟨scale c ^ (q c), pow_nonneg (hscale c).le _⟩)
      (C.densityClockClassKinetic (Q c) (reference c).val density)
      (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt / scale c ^ (q c)
  let bound := fun (c : Cells) ↦ volume.real ((coord c) '' cell c) * rate c + ε c * |rate c| +
    activeGridRepairError (q c) (legalGridRepairConstant (q c) ((Q c).count + 1) ((Q c).count * (Q c).count))
      (B c) ‖f‖ tilt 1 ((scale c / (2 * (R c : ℝ))) ^ (q c))
  have hI : ∀ᶠ N : ℕ in atTop, ∀ c, Integrable (value c N) ((Refined N).markedLaw N) :=
    Filter.eventually_all.mpr (fun c ↦ (hlocal c G hG (htrace c) tilt).1)
  have hglobal (N : ℕ) (hN : ∀ c, Integrable (value c N) ((Refined N).markedLaw N)) :
      Integrable (original N) ((Refined N).markedLaw N) ∧
        (∫ sample, original N sample ∂(Refined N).markedLaw N) =
          ∑ c, ∫ sample, value c N sample ∂(Refined N).markedLaw N :=
    D.original_model_family_integral_eq_seed_sum coreIndex Q reference classify cell f tilt
      ((Refined N).markedLaw N) hN
  refine ⟨hI.mono (fun N hN ↦ (hglobal N hN).1),?_⟩
  intro ζ hζ
  let tol := ζ / ((Fintype.card Cells : ℝ) + 1)
  have htol : 0 < tol := div_pos hζ (by positivity)
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ c,
      (∫ sample, value c N sample ∂(Refined N).markedLaw N) / N ≤ bound c + tol :=
    Filter.eventually_all.mpr (fun c ↦ (hlocal c G hG (htrace c) tilt).2 tol htol)
  filter_upwards [hI,hevent] with N hIN hN
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hN c)
  have htolSum : (∑ _ : Cells, tol) ≤ ζ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      (Fintype.card Cells : ℝ) * tol ≤ ((Fintype.card Cells : ℝ) + 1) * tol :=
        mul_le_mul_of_nonneg_right (by linarith) htol.le
      _ = ζ := by dsimp only [tol]; field_simp
  calc
    _ = ∑ c, (∫ sample, value c N sample ∂(Refined N).markedLaw N) / N := by
      rw [(hglobal N hIN).2, Finset.sum_div]
    _ ≤ ∑ c, (bound c + tol) := hsum
    _ = (∑ c, bound c) + ∑ _ : Cells, tol := Finset.sum_add_distrib
    _ ≤ (∑ c, bound c) + ζ := add_le_add (le_refl _) htolSum

end OTSelector.Reconstruction
