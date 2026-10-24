import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveValue
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveCarrier
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalIntegrability

/-! The original canonical macrocell model mean is an exact paired-class iid mean. -/
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


theorem PopulationLocalPressureCore.actual_original_paired_active_model_mean_of_classifier
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
    (ref : (D.haar.continuous.coefficient i).roots) (f : M × M →ᵇ ℝ)
    (N : ℕ) (scale tilt : ℝ) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue Seed a
    let m := (κ C.seedIndex).restrict (R '' L)
    let atomic := clockClassPairMeasure P₀
    let spatial := originalRetainedSpatialLaw m (atomic univ)
    let common := spatial.prod (clockClassJointProbability P₀ hP₀ hmass : Measure (Fin Q.count × Fin Q.count))
    let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let original := originalRetainedSeedClassCost a L (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      scale (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) tilt
    let latent := fun sample ↦ PartialMatching.legalMaximumValue
      (pairedClassActiveGraph (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ()))
        (C.clockClassAllowed Q) sample.1 sample.2)
      (fun j k ↦ scale * C.clockClassKinetic Q ref.val (sample.1 j).2.1 (sample.2 k).2.2
        (e ((sample.2 k).1.elim 0 id - (sample.1 j).1.elim 0 id)) +
        tilt * C.clockClassProbe Q ref.val ref.property f (sample.1 j).2.1 (sample.2 k).2.2)
    m univ * atomic univ ≤ 1 ∧ IsProbabilityMeasure spatial ∧
      (∀ᵐ o ∂spatial, ∀ w, o = some w → w ∈ R '' C.roots) ∧
      Integrable original (Refined.markedLaw N) ∧ Integrable latent law ∧
      (Refined.markedLaw N).map original = law.map latent ∧
      (∫ sample, original sample ∂Refined.markedLaw N) = ∫ sample, latent sample ∂law := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
  let R := populationSeedRootLabelValue Seed a
  let m := (κ C.seedIndex).restrict (R '' L)
  let atomic := clockClassPairMeasure P₀
  let spatial := originalRetainedSpatialLaw m (atomic univ)
  let common := spatial.prod (clockClassJointProbability P₀ hP₀ hmass : Measure (Fin Q.count × Fin Q.count))
  let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  let Refined := Cst.refineSubplan ξG hξG
  let read := fun p : M × Option (Bool × T) ↦
    if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (R (a p.1),classify (u p.1)) else none
  let observe := Prod.map (fun xs : Fin N → M × Option (Bool × T) ↦ fun j ↦ read (xs j))
    (fun ys : Fin N → M × Option (Bool × T) ↦ fun k ↦ read (ys k))
  let forget := Prod.map
    (fun xs : Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count) ↦
      fun j ↦ pairedActiveSourceRead (xs j))
    (fun ys : Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count) ↦
      fun k ↦ pairedActiveTargetRead (ys k))
  let score := fun (p : Seed.covector.ker × Fin Q.count) (p' : Seed.covector.ker × Fin Q.count) ↦
    scale * C.clockClassKinetic Q ref.val p.2 p'.2 (e (p'.1 - p.1)) +
      tilt * C.clockClassProbe Q ref.val ref.property f p.2 p'.2
  let value := optionalClassValue (m := N) (n := N) (classify 0) (classify 0) (C.clockClassAllowed Q) score
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hread : Measurable read := (MeasureTheory.Option.measurable_some.comp
    ((hR.comp (ha.comp measurable_fst)).prodMk
      (hm.comp (hu.continuous.measurable.comp measurable_fst)))).ite
        (measurableSet_retainedMarkedCellEvent (ha hL)) measurable_const
  have hobserve : Measurable observe :=
    (measurable_pi_lambda _ (fun j ↦ hread.comp (measurable_pi_apply j))).prodMap
      (measurable_pi_lambda _ (fun k ↦ hread.comp (measurable_pi_apply k)))
  have hforget : Measurable forget :=
    (measurable_pi_lambda _ (fun j ↦ measurable_pairedActiveSourceRead.comp (measurable_pi_apply j))).prodMap
      (measurable_pi_lambda _ (fun k ↦ measurable_pairedActiveTargetRead.comp (measurable_pi_apply k)))
  have hscore : Measurable (Function.uncurry score) := by
    have hc : Measurable (fun p : (Seed.covector.ker × Fin Q.count) × (Seed.covector.ker × Fin Q.count) ↦
        (p.1.2,p.2.2)) := by fun_prop
    have hv : Measurable (fun p : (Seed.covector.ker × Fin Q.count) × (Seed.covector.ker × Fin Q.count) ↦
        e (p.2.1-p.1.1)) := by fun_prop
    exact (((C.measurable_clockClassKinetic Q ref.val).comp (hc.prodMk hv)).const_mul scale).add
      (((C.measurable_clockClassProbe Q ref.val ref.property f).comp hc).const_mul tilt)
  have hvalue : Measurable value := measurable_optionalClassValue _ _ _ hscore
  have hobs := D.actual_original_paired_active_observation_of_classifier hF hcomplete hu ha hinj
    i hL hsub hG hLG Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf
    hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv
    hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst
  have hlaw : (Refined.markedLaw N).map observe = law.map forget := hobs.2.2.2.2 N
  have horiginal : (fun sample ↦ value (observe sample)) =
      originalRetainedSeedClassCost a L (fun x ↦ R (a x)) e.toLinearMap
        (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
        scale (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) tilt := by
    funext sample
    exact (originalRetainedSeedClassCost_eq_optionalClassValue a L (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (classify 0) (classify 0) _
      scale _ _ tilt sample).symm
  have hlatent := fun sample ↦ optionalClassValue_paired_read_eq (m := N) (n := N) (classify 0) (classify 0)
    (C.clockClassAllowed Q) e.toLinearMap scale (C.clockClassKinetic Q ref.val)
      (C.clockClassProbe Q ref.val ref.property f) tilt sample
  have hi := D.original_canonical_seed_cost_integrable hF hcomplete hu ha hinj i Q ref f
    hL hsub classify hm hπWhole Cst ξG hξG N scale tilt
  have hiobs : Integrable value ((Refined.markedLaw N).map observe) := by
    rw [integrable_map_measure hvalue.aestronglyMeasurable hobserve.aemeasurable]
    simpa only [Function.comp_def,horiginal] using hi
  have hilat : Integrable value (law.map forget) := hlaw ▸ hiobs
  have hilat' : Integrable (fun sample ↦ value (forget sample)) law :=
    hilat.comp_measurable hforget
  refine ⟨hobs.1,hobs.2.1,D.original_retained_spatial_root_carrier hcomplete i hL hsub _,hi,?_,?_,?_⟩
  · exact hilat'.congr (Filter.Eventually.of_forall hlatent)
  · have hv := congrArg (fun μ ↦ μ.map value) hlaw
    rw [Measure.map_map hvalue hobserve,Measure.map_map hvalue hforget] at hv
    simp only [Function.comp_def,horiginal] at hv
    exact hv.trans (Measure.map_congr (μ := law) (Filter.Eventually.of_forall hlatent))
  · calc
      _ = ∫ sample, value (observe sample) ∂Refined.markedLaw N := by rw [horiginal]
      _ = ∫ v, value v ∂(Refined.markedLaw N).map observe :=
        (integral_map hobserve.aemeasurable hiobs.aestronglyMeasurable).symm
      _ = ∫ v, value v ∂law.map forget := by rw [hlaw]
      _ = ∫ sample, value (forget sample) ∂law := integral_map hforget.aemeasurable hilat.aestronglyMeasurable
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hlatent)

end OTSelector.Reconstruction
