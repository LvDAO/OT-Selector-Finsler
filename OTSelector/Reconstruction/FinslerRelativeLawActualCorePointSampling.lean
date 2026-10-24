import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Probability.TypedPopulationSampling
import OTSelector.Geometry.FinslerDistanceLocalizationPopulation

/-! Actual original samples over retained roots are the same seed endpoints
used by the legal finite class competitor. -/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Conditional recovery on a cell yields original physical recovery there,
using the given original almost-everywhere inverse. -/
theorem ae_original_recovery_of_condDistrib_cell
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq X]
    (μ : Measure X) [IsFiniteMeasure μ] (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b c : Z × ℝ → X) (hb : Measurable b) (hc : Measurable c)
    (hlabel : μ.map a = lambda) (hinv : ∀ᵐ x ∂μ, b (a x, u x) = x)
    {L : Set Z} (hL : MeasurableSet L)
    (hfields : ∀ᵐ z ∂lambda.restrict L, ∀ᵐ t ∂condDistrib u a μ z, b (z, t) = c (z, t)) :
    ∀ᵐ x ∂μ, a x ∈ L → c (a x, u x) = x := by
  have hcomp : ∀ᵐ p ∂lambda.restrict L ⊗ₘ condDistrib u a μ, b p = c p :=
    Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hb hc) hfields
  have hjoint := original_label_clock_restrict_eq_compProd μ ha hu hL
  rw [hlabel] at hjoint
  rw [← hjoint] at hcomp
  have hp := ae_of_ae_map (ha.prodMk hu).aemeasurable hcomp
  have hcell : ∀ᵐ x ∂μ.restrict (a ⁻¹' L), c (a x, u x) = x := by
    filter_upwards [hp, ae_restrict_of_ae hinv] with x hx hi
    exact hx.symm.trans hi
  exact ae_imp_of_ae_restrict hcell

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Every original physical sample on an actual retained root cell is the
literal endpoint used by the original finite class geometry, including clocks
outside its paired coefficient window. -/
theorem PopulationLocalPressureCore.original_cell_corePoint_ae
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ y ∂η₁, y ∈ F.potentialRegularDomain u)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) :
    (∀ᵐ x ∂η₀, a x ∈ L → D.corePoint i (a x, u x) = x) ∧
    (∀ᵐ y ∂η₁, a y ∈ L → D.corePoint i (a y, u y) = y) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let c := fun q : (ℚ → M) × ℝ ↦ populationSeedPhysicalMap Seed (R q.1, q.2)
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hc : Measurable c := (measurable_populationSeedPhysicalMap Seed).comp
    ((hR.comp measurable_fst).prodMk measurable_snd)
  have hpoint (z) (hz : z ∈ L) (t : ℝ) : c (z, t) = D.corePoint i (z, t) := by
    have hzI : z ∈ (D.haar.intensity i).roots := by
      rw [D.haar.intensity_roots]
      exact hsub hz
    let w : Seed.labels := ⟨R z, (D.haar.intensity i).labels_subset (mem_image_of_mem R hzI)⟩
    exact populationSeedPhysicalMap_at_label Seed w t
  have hcurve := D.haar.original_inverse_ae_of_ae_recovery hF hcomplete hu ha hinj horder hb
    hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1 i
  have hfields : ∀ᵐ z ∂lambda.restrict L,
      (∀ᵐ s ∂condDistrib u a η₀ z, b (z, s) = c (z, s)) ∧
      (∀ᵐ t ∂condDistrib u a η₁ z, b (z, t) = c (z, t)) := by
    filter_upwards [ae_restrict_mem hL, ae_restrict_of_ae_restrict_of_subset hsub hcurve] with z hz he
    constructor
    · filter_upwards [he.1] with t ht
      exact ht.trans (hpoint z hz t).symm
    · filter_upwards [he.2] with t ht
      exact ht.trans (hpoint z hz t).symm
  have hs := ae_original_recovery_of_condDistrib_cell η₀ lambda a u ha hu.continuous.measurable
    b c hb hc hlabel0 hη₀inv hL (hfields.mono fun _ h ↦ h.1)
  have ht := ae_original_recovery_of_condDistrib_cell η₁ lambda a u ha hu.continuous.measurable
    b c hb hc hlabel1 hη₁inv hL (hfields.mono fun _ h ↦ h.2)
  exact ⟨hs.mono fun x hx hz ↦ (hpoint (a x) hz (u x)).symm.trans (hx hz),
    ht.mono fun y hy hz ↦ (hpoint (a y) hz (u y)).symm.trans (hy hz)⟩

/-- On one common event, every original marked sample in the actual root
cell is the same physical seed endpoint, before choosing any retained subcloud
or sample-dependent legal matching. -/
theorem PopulationLocalPressureCore.original_marked_iid_cell_corePoint_ae
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ y ∂η₁, y ∈ F.potentialRegularDomain u)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {πWhole : Measure (M × M)} [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    {T : Type*} [Fintype T] [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (Types : PopulationSubcouplingTypes πWhole T)
    {NS NT : Type*} [Fintype NS] [Fintype NT] :
    ∀ᵐ sample ∂(Measure.pi (fun _ : NS ↦ Types.sourceMarkedLaw η₀)).prod
      (Measure.pi (fun _ : NT ↦ Types.targetMarkedLaw η₁)),
      (∀ j, a (sample.1 j).1 ∈ L →
        D.corePoint i (a (sample.1 j).1, u (sample.1 j).1) = (sample.1 j).1) ∧
      (∀ k, a (sample.2 k).1 ∈ L →
        D.corePoint i (a (sample.2 k).1, u (sample.2 k).1) = (sample.2 k).1) := by
  obtain ⟨hs, ht⟩ := D.original_cell_corePoint_ae hF hcomplete hu ha hinj horder hb
    hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1 i hL hsub
  have hsource : ∀ᵐ x ∂Measure.pi (fun _ : NS ↦ η₀),
      ∀ j, a (x j) ∈ L → D.corePoint i (a (x j), u (x j)) = x j :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval (fun _ : NS ↦ η₀) j).ae hs
  have htarget : ∀ᵐ y ∂Measure.pi (fun _ : NT ↦ η₁),
      ∀ k, a (y k) ∈ L → D.corePoint i (a (y k), u (y k)) = y k :=
    ae_all_iff.mpr fun k ↦ (Measure.quasiMeasurePreserving_eval (fun _ : NT ↦ η₁) k).ae ht
  apply Types.iid_original_physical_property (I := NS) (J := NT) hπWhole
    (fun sample : (NS → M) × (NT → M) ↦
      (∀ j, a (sample.1 j) ∈ L → D.corePoint i (a (sample.1 j), u (sample.1 j)) = sample.1 j) ∧
      (∀ k, a (sample.2 k) ∈ L → D.corePoint i (a (sample.2 k), u (sample.2 k)) = sample.2 k))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsource,
    Measure.quasiMeasurePreserving_snd.ae htarget] with sample hs ht
  exact ⟨hs, ht⟩

end OTSelector.Reconstruction
