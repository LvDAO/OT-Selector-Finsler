import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedSpatialMacrocell
import OTSelector.Probability.HaarAffineUnitPartition

/-! A literal physical microbox reads the same original retained cloud and
its paired-class experiment. Counts, marks and raw displacement stay unchanged. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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


/-- The exact original canonical microcell mean is the physical-box block of
its whole macrocell paired experiment, for the same given classifier. -/
theorem PopulationLocalPressureCore.actual_original_physical_microcell_mean
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {G : Set (ℚ → M)} (hG : MeasurableSet G)
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
    (ref : (D.haar.continuous.coefficient i).roots) (f : M × M →ᵇ ℝ)
    (N : ℕ) (scale tilt : ℝ) (n : ℕ) [NeZero n]
    (ν : Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℤ) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
    let root := populationSeedRootLabelValue Seed a
    let spatial := originalRetainedSpatialLaw ((κ C.seedIndex).restrict (root '' (L ∩ G)))
      ((clockClassPairMeasure P₀) univ)
    let common := spatial.prod (clockClassJointProbability P₀ hP₀ hmass : Measure (Fin Q.count × Fin Q.count))
    let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let original := originalRetainedSeedClassCost a
      (L ∩ (e ∘ root) ⁻¹' (BoxIntegral.unitPartition.box n ν : Set (Fin _ → ℝ)))
      (fun x ↦ root (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      scale (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) tilt
    let latent := fun sample ↦ PartialMatching.legalMaximumValue
      ((pairedClassActiveGraph (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ()))
        (C.clockClassAllowed Q) sample.1 sample.2).filter (fun edge ↦
        e ((sample.1 edge.1).1.elim 0 id) ∈ BoxIntegral.unitPartition.box n ν ∧
        e ((sample.2 edge.2).1.elim 0 id) ∈ BoxIntegral.unitPartition.box n ν))
      (fun j k ↦ scale * C.clockClassKinetic Q ref.val (sample.1 j).2.1 (sample.2 k).2.2
        (e ((sample.2 k).1.elim 0 id - (sample.1 j).1.elim 0 id)) +
        tilt * C.clockClassProbe Q ref.val ref.property f (sample.1 j).2.1 (sample.2 k).2.2)
    Integrable original (Refined.markedLaw N) ∧ Integrable latent law ∧
      (∫ sample, original sample ∂Refined.markedLaw N) = ∫ sample, latent sample ∂law := by
  classical
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
  let root := populationSeedRootLabelValue Seed a
  let label : Seed.covector.ker → Bool := fun w ↦
    if e w ∈ BoxIntegral.unitPartition.box n ν then true else false
  have hlabel : Measurable label := measurable_const.ite
    ((BoxIntegral.unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable) measurable_const
  have hmean := D.actual_original_paired_spatial_macrocell_mean_of_classifier hF hcomplete hu ha hinj
    i hL hsub hG Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf
    hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv
    hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref f N scale tilt label hlabel true
  have hset : L ∩ (label ∘ root) ⁻¹' {true} =
      L ∩ (e ∘ root) ⁻¹' (BoxIntegral.unitPartition.box n ν : Set (Fin _ → ℝ)) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Function.comp_apply,label]
    split_ifs <;> simp_all
  have hgraph (sample : (Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count)) ×
      (Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count))) :
      PartialMatching.spatialLegalBlock
        (pairedClassActiveGraph (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ()))
          (C.clockClassAllowed Q) sample.1 sample.2)
        (fun j ↦ label ((sample.1 j).1.elim 0 id))
        (fun k ↦ label ((sample.2 k).1.elim 0 id)) true =
      (pairedClassActiveGraph (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ()))
          (C.clockClassAllowed Q) sample.1 sample.2).filter (fun edge ↦
        e ((sample.1 edge.1).1.elim 0 id) ∈ BoxIntegral.unitPartition.box n ν ∧
        e ((sample.2 edge.2).1.elim 0 id) ∈ BoxIntegral.unitPartition.box n ν) := by
    ext edge
    simp only [PartialMatching.spatialLegalBlock,Finset.mem_filter,label]
    split_ifs <;> simp_all
  have hraw := And.intro hmean.2.2.2.1
    (And.intro hmean.2.2.2.2.1 hmean.2.2.2.2.2.2)
  dsimp only [root,e,Seed,C] at hset hgraph
  simpa only [hset,hgraph] using hraw

end OTSelector.Reconstruction
