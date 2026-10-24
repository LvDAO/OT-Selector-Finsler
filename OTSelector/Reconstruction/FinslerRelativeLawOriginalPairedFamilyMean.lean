import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveMacrocell
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedMicrocellShapeExpectation
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelUniformBound

/-! One original rebuilt population supplies all dependent paired-cell means. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
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

/-- The exact nullable spatial factor of one original retained macrocell. -/
def PopulationLocalPressureCore.originalPairedClockClassSpatialLaw
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (L G : Set (ℚ → M)) : Measure (Option (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) :=
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  originalRetainedSpatialLaw ((κ C.seedIndex).restrict (R '' (L ∩ G))) ((clockClassPairMeasure P₀) univ)

/-- The entire paired-class cloud for one fixed macrocell and one deterministic
retained restriction. Its activity probability is derived by the actual law theorem. -/
def PopulationLocalPressureCore.originalPairedClockClassLaw
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (L G : Set (ℚ → M)) (N : ℕ) :
    let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
    Measure ((Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count)) ×
      (Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count))) :=
  let spatial := D.originalPairedClockClassSpatialLaw i Q P₀ L G
  let common := spatial.prod (normalizedClockClassPairMeasure P₀)
  (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))

/-- The original untruncated class value on the entire paired-cell arrays. -/
def PopulationLocalPressureCore.originalPairedClockClassValue
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (ref : (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ) (N : ℕ) (scale tilt : ℝ) :
    let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
    ((Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count)) ×
      (Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count))) → ℝ :=
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let basis := Module.finBasis ℝ Seed.covector.ker
  fun sample ↦ PartialMatching.legalMaximumValue
    (pairedClassActiveGraph (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ()))
      (C.clockClassAllowed Q) sample.1 sample.2)
    (fun j k ↦ scale * C.clockClassKinetic Q ref.val (sample.1 j).2.1 (sample.2 k).2.2
      (basis.equivFun ((sample.2 k).1.elim 0 id - (sample.1 j).1.elim 0 id)) +
      tilt * C.clockClassProbe Q ref.val ref.property f (sample.1 j).2.1 (sample.2 k).2.2)

/-- The global original canonical model mean is a finite sum of the literal
paired-cell means. All cells use one original residual experiment and one typed
atlas; the independent latent laws are used only to read the separate integrals. -/
theorem PopulationLocalPressureCore.actual_original_paired_family_mean_of_classifier
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {Cells : Type*} [Fintype Cells] (coreIndex : Cells → Fin D.haar.continuous.count)
    {range : Set ℝ} {width : ℝ} (Q : Cells → FiniteScalarBins range width)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (hm : ∀ c, Measurable (classify c))
    (hclass : ∀ c j x, x ∈ (Q c).cell j → classify c x = j)
    (fallbackS fallbackT : ∀ c, Fin (Q c).count → ℝ)
    (P₀ : ∀ c, Fin (Q c).count → Fin (Q c).count → ℝ)
    (hP₀ : ∀ c j k, 0 ≤ P₀ c j k) (hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k)
    (Pf residual : ∀ c, (ℚ → M) → Fin (Q c).count → Fin (Q c).count → ℝ)
    (hmPf : ∀ c j k, Measurable (fun z ↦ Pf c z j k))
    (hPf : ∀ c z, z ∈ cell c → ∀ j k, Pf c z j k = P₀ c j k / D.rootIntensity (coreIndex c) z)
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j, ∑ k, (Pf c z j k + residual c z j k) =
      (condDistrib u a η₀ z).real ((Q c).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ k, ∑ j, (Pf c z j k + residual c z j k) =
      (condDistrib u a η₁ z).real ((Q c).cell k))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (hK : ∀ c, K c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) ((Q c).cell j) ((Q c).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) ((Q c).cell k) ((Q c).measurable_cell k) (fallbackT c k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x,u x) = x) (hη₁inv : ∀ᵐ y ∂η₁, b (a y,u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (πWhole ξ : Measure (M × M)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {T : Type*} [Fintype T] {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T q cost)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    {G : Set (ℚ → M)} (hG : MeasurableSet G) (f : M × M →ᵇ ℝ) (N : ℕ) (tilt : ℝ) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let original := D.originalClockClassOldModelValue (q := q) (n := N)
      coreIndex Q reference classify cell f tilt (T := T)
    let law := fun c ↦ D.originalPairedClockClassLaw (coreIndex c) (Q c) (P₀ c) (cell c) G N
    let value := fun c ↦ D.originalPairedClockClassValue (coreIndex c) (Q c) (reference c) f N
      ((N : ℝ) ^ (2 / (q : ℝ))) tilt
    (∀ c, IsProbabilityMeasure (D.originalPairedClockClassSpatialLaw (coreIndex c) (Q c) (P₀ c) (cell c) G) ∧
      (∀ᵐ o ∂D.originalPairedClockClassSpatialLaw (coreIndex c) (Q c) (P₀ c) (cell c) G,
        ∀ w, o = some w → w ∈ populationSeedRootLabelValue
          (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed a ''
            (D.haar.continuous.coefficient (coreIndex c)).roots)) ∧
    Integrable original (Refined.markedLaw N) ∧
      (∀ c, Integrable (value c) (law c)) ∧
      (∫ sample, original sample ∂Refined.markedLaw N) = ∑ c, ∫ sample, value c sample ∂law c := by
  classical
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  let Refined := Cst.refineSubplan ξG hξG
  let old := fun c ↦
    let C := D.haar.continuous.coefficient (coreIndex c)
    let Seed := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue Seed a
    originalRetainedSeedClassCost a (cell c) (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify c (u x)) (fun x ↦ classify c (u x)) (C.clockClassAllowed (Q c))
      ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic (Q c) (reference c).val)
      (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt (T := T) (N := N)
  have hmean c := D.actual_original_paired_active_macrocell_mean_of_classifier hF hcomplete hu ha hinj
    (coreIndex c) (hcell c) (hsub c) hG (Q c) (classify c) (hm c) (hclass c)
    (fallbackS c) (fallbackT c) (P₀ c) (hP₀ c) (hmass c) (Pf c) (residual c) (hmPf c)
    (hPf c) (hresidual c) (hrow c) (hcol c) cell hcell hdisj K c (Subset.rfl) (hK c)
    Qglobal hwhole hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst
    (reference c) f N ((N : ℝ) ^ (2 / (q : ℝ))) tilt
  have hi : ∀ c, Integrable (old c) (Refined.markedLaw N) := fun c ↦ (hmean c).2.2.2.1
  have heq : D.originalClockClassOldModelValue (q := q) (n := N)
      coreIndex Q reference classify cell f tilt (T := T) = fun sample ↦ ∑ c, old c sample := by
    funext sample
    apply Finset.sum_congr rfl
    intro c _
    exact D.original_clockClass_canonical_cost_eq_seed coreIndex reference Q classify f cell c _ tilt sample
  refine ⟨fun c ↦ ⟨(hmean c).2.1,(hmean c).2.2.1⟩,?_,fun c ↦ (hmean c).2.2.2.2.1,?_⟩
  · rw [heq]
    exact integrable_finsetSum _ (fun c _ ↦ hi c)
  · rw [heq,integral_finsetSum _ (fun c _ ↦ hi c)]
    exact Finset.sum_congr rfl (fun c _ ↦ (hmean c).2.2.2.2.2.2)

end OTSelector.Reconstruction
