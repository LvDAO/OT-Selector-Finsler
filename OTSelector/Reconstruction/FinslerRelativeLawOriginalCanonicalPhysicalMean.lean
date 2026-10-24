import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalForwardGeometry
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalIntegrability
import OTSelector.Reconstruction.FinslerRelativeLawOriginalClassifiedForwardGeometry
import OTSelector.Reconstruction.FinslerRelativeLawActualCorePointSampling
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergy
import OTSelector.Reconstruction.FinslerRelativeLawOriginalEveryClassOptimizer
import OTSelector.Reconstruction.FinslerRelativeLawOriginalClassifiedOptimizers
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalPrefixEmbedding
import OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassMembership
import OTSelector.Reconstruction.FinslerConcreteUpperClassCompetitor

/-! Actual original retained samples receive the legal finite class competitor
on their same original indices, while every global residual mark stays separate. -/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false

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

/-- The actual geometry and unchanged original marked experiment give an
integrable physical canonical competitor and its precise relative model-mean
upper bound. The matched-cardinality probe error is retained for disjoint
cell summation; all optimizer measurability and integrability are internal. -/
theorem PopulationLocalPressureCore.exists_original_canonical_cell_physical_expectation
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a η₀) (condDistrib u a η₁) originalGap I) r δ loss)
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

    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ y ∂η₁, y ∈ B)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobeError : 0 < probeError)
 :

    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ ref, IsOpen (U ref) ∧ ref.val ∈ U ref) ∧
      (∀ z₀ j k, C.clockClassAllowed (Q z₀) j k →
        ∀ s ∈ (Q z₀).cell j, ∀ t ∈ (Q z₀).cell k,
          s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1) ∧
      (∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
        ∀ s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
        ∀ t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
          s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
          (s, t) ∈ C.window.region) ∧
      (∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
      ∀ j k, C.clockClassAllowed (Q z₀) j k → ∀ s ∈ (Q z₀).cell j,
      ∀ t ∈ (Q z₀).cell k,
      D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        let S := (P C.seedIndex).seed
        let R := populationSeedRootLabelValue S a
        let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
        (s, t) ∈ C.window.region ∧
        |populationSeedPairDeficit S (s, t) (R z, R z') -
          C.clockClassKinetic (Q z₀) z₀.val j k v| ≤
            (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q z₀) z₀.val j k v ∧
        |f (D.corePoint i (z, s), D.corePoint i (z', t)) -
          C.clockClassProbe (Q z₀) z₀.val z₀.property f j k| ≤ 2 * probeError) ∧
      ∀ (πWhole : Measure (M × M)) [IsFiniteMeasure πWhole]
      (_hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
      {T : Type*} [Fintype T]
      (Cst : PopulationTypedCostData πWhole η₀ η₁ T q
        (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
      (ξ : Measure (M × M)) (hξ : ξ ≤ πWhole)
      [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))],
      let Refined := Cst.refineSubplan ξ hξ
      ∀ (N : ℕ) (ref : C.roots) (classify : ℝ → Fin (Q ref).count), Measurable classify →
      (∀ j x, x ∈ (Q ref).cell j → classify x = j) →
      ∀ (L : Set (ℚ → M)), MeasurableSet L → L ⊆ C.roots ∩ U ref → ∀ tilt : ℝ,
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let e := (Module.finBasis ℝ S.covector.ker).equivFunL
      let extra := fun (_ : Unit) (cloud : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
        C.clockClassAllowed (Q ref) (classify (u (cloud.1 jk.1).1)) (classify (u (cloud.2 jk.2).1)))
      let model := fun (_ : Unit) (cloud : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) j k ↦
        (N : ℝ) ^ (2 / (q : ℝ)) * C.clockClassKinetic (Q ref) ref.val
          (classify (u (cloud.1 j).1)) (classify (u (cloud.2 k).1))
          (e (R (a (cloud.2 k).1) - R (a (cloud.1 j).1))) +
        tilt * C.clockClassProbe (Q ref) ref.val ref.property f
          (classify (u (cloud.1 j).1)) (classify (u (cloud.2 k).1))
      let σ := originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra model ()
      let physical := fun sample ↦ (σ sample).cost (fun j k ↦
        (N : ℝ) ^ (2 / (q : ℝ)) * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
          u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1))
      let frozen := fun sample ↦ (σ sample).cost (model () sample)
      Integrable physical (Refined.markedLaw N) ∧ Integrable frozen (Refined.markedLaw N) ∧
      Integrable (fun sample ↦ ((σ sample).card : ℝ)) (Refined.markedLaw N) ∧
      (∫ sample, physical sample ∂Refined.markedLaw N) ≤
        (1 + (3 * ε + 2 * ε ^ 2)) * (∫ sample, frozen sample ∂Refined.markedLaw N) +
        (∫ sample, ((σ sample).card : ℝ) ∂Refined.markedLaw N) *
          (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨Q, U, hU, houter, hregion, hgeometry, hcompare⟩ :=
    D.exists_original_canonical_cell_physical_comparison_with_forward_geometry γ originalGap
      hF hcomplete hu ha hinj horder hb hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1
      i f hgap hsep hη₀A hη₁B hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, houter, hregion, hgeometry, ?_⟩
  intro πWhole _ hπWhole T _ Cst ξ hξ _ _
  let Refined := Cst.refineSubplan ξ hξ
  dsimp only
  intro N ref classify hm hclass L hL hsub tilt
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let extra := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
    C.clockClassAllowed (Q ref) (classify (u (sample.1 jk.1).1)) (classify (u (sample.2 jk.2).1)))
  let model := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) j k ↦ (N : ℝ) ^ (2 / (q : ℝ)) * C.clockClassKinetic (Q ref) ref.val
      (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
      (e (R (a (sample.2 k).1) - R (a (sample.1 j).1))) +
      tilt * C.clockClassProbe (Q ref) ref.val ref.property f
        (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
  let σ := originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra model ()
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have huM : Measurable u := hu.continuous.measurable
  have hmodel : ∀ (_c : Unit) j k, Measurable (fun sample ↦ model _c sample j k) := by
    intro _ j k
    have hs : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦ classify (u (sample.1 j).1)) := by fun_prop
    have ht : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦ classify (u (sample.2 k).1)) := by fun_prop
    have hv : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦ e (R (a (sample.2 k).1) - R (a (sample.1 j).1))) := by fun_prop
    exact (((C.measurable_clockClassKinetic (Q ref) ref.val).comp ((hs.prodMk ht).prodMk hv)).const_mul _).add
      (((C.measurable_clockClassProbe (Q ref) ref.val ref.property f).comp (hs.prodMk ht)).const_mul tilt)
  have hextra : ∀ (_c : Unit) V, MeasurableSet {sample | extra _c sample = V} := by
    intro _ V
    have hclasses : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦
      ((fun j : Fin N ↦ classify (u (sample.1 j).1)), (fun k : Fin N ↦ classify (u (sample.2 k).1)))) := by fun_prop
    exact ((measurable_of_countable (fun classes : (Fin N → Fin (Q ref).count) × (Fin N → Fin (Q ref).count) ↦
      Finset.univ.filter (fun jk : Fin N × Fin N ↦ C.clockClassAllowed (Q ref) (classes.1 jk.1) (classes.2 jk.2)))).comp hclasses)
        (measurableSet_singleton V)
  have hσ := measurableSet_mem_originalRetainedCellOptimizer a ha (fun _ : Unit ↦ L) (fun _ ↦ hL)
    extra hextra model hmodel ()
  letI : IsProbabilityMeasure (Refined.markedLaw N) := (Refined.iid_facts hπWhole N).1
  have Icard := OTSelector.PartialMatching.integrable_sample_card_of_edge_events (Refined.markedLaw N) σ hσ
  have Imodel := D.original_canonical_seed_cost_integrable hF hcomplete hu ha hinj i (Q ref) ref f hL
    (fun z hz ↦ (hsub hz).1) classify hm hπWhole Cst ξ hξ N ((N : ℝ) ^ (2 / (q : ℝ))) tilt
  have Iphysical := OTSelector.PartialMatching.integrable_sample_cost_of_edge_events (Refined.markedLaw N) σ hσ _
    (Cst.original_marked_tilted_edge_integrable hπWhole ξ hξ N (fun x y ↦ f (x, y))
      f.continuous.measurable (Filter.Eventually.of_forall fun p ↦ by
        simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm p) tilt)
  have hpoint : ∀ᵐ sample ∂Refined.markedLaw N,
      (σ sample).cost (fun j k ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
        ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal - u (sample.2 k).1 + u (sample.1 j).1) +
        tilt * f ((sample.1 j).1, (sample.2 k).1)) ≤
      (1 + (3 * ε + 2 * ε ^ 2)) * (σ sample).cost (model () sample) +
        ((σ sample).card : ℝ) * (|tilt| * (2 * probeError) +
          (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) := by
    filter_upwards [hcompare πWhole hπWhole Cst ξ hξ N] with sample hs
    have hc := hs ref classify hclass L hsub ((N : ℝ) ^ (2 / (q : ℝ))) (by positivity) tilt
    have hv := (originalRetainedCellOptimizer_isLegalOptimal a (fun _ : Unit ↦ L) extra model () sample).2.2.trans
      (originalRetainedCellGraph_value_eq_prefix a (fun _ : Unit ↦ L) extra model () sample)
    have hrank := (originalRetainedCellOptimizer_isLegalOptimal a (fun _ : Unit ↦ L) extra model () sample).2.1.trans
      (originalRetainedCellGraph_card_eq_prefix a (fun _ : Unit ↦ L) extra () sample)
    change (σ sample).cost (fun j k ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
      ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal - u (sample.2 k).1 + u (sample.1 j).1) +
      tilt * f ((sample.1 j).1, (sample.2 k).1)) ≤
      (1 + (3 * ε + 2 * ε ^ 2)) *
        PartialMatching.legalMaximumValue (PartialMatching.inducedLegalGraph (extra () sample)
          (finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.1)
          (finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.2))
          (fun j k ↦ model () sample
            (finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.1 j)
            (finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.2 k)) +
      (PartialMatching.legalMaximumCard (PartialMatching.inducedLegalGraph (extra () sample)
        (finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.1)
        (finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.2)) : ℝ) *
        (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) at hc
    rw [← hv, ← hrank] at hc
    exact hc
  have Imodel' : Integrable (fun sample ↦ (σ sample).cost (model () sample)) (Refined.markedLaw N) := Imodel
  have Iright := (Imodel'.const_mul (1 + (3 * ε + 2 * ε ^ 2))).add
    (Icard.mul_const (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)))
  have hle := integral_mono_ae Iphysical Iright hpoint
  refine ⟨Iphysical, Imodel', Icard, ?_⟩
  change _ ≤ ∫ sample, (1 + (3 * ε + 2 * ε ^ 2)) * (σ sample).cost (model () sample) +
    ((σ sample).card : ℝ) * (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
      ∂Refined.markedLaw N at hle
  rw [integral_add (Imodel'.const_mul (1 + (3 * ε + 2 * ε ^ 2)))
    (Icard.mul_const (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))),
    integral_const_mul, integral_mul_const] at hle
  exact hle

end OTSelector.Reconstruction
