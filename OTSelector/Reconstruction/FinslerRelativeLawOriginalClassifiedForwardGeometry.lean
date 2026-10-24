import OTSelector.Reconstruction.FinslerRelativeLawOriginalEveryClassForwardGeometry
import OTSelector.Reconstruction.FinslerRelativeLawActualCorePointSampling
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergy
import OTSelector.Reconstruction.FinslerRelativeLawOriginalEveryClassOptimizer
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

/-- Every original frozen optimizer obeys the actual physical comparison
using the literal classifier produced by the original class-law construction.
The full original conditional clock range discharges all raw-bin membership
premises, on one event before every subcloud or matching is selected. -/
theorem PopulationLocalPressureCore.exists_original_marked_classified_clockClass_optimizers_with_forward_geometry
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
      {T : Type*} [Fintype T] {q : ℕ} {cost : M → M → ℝ}
      (Cst : PopulationTypedCostData πWhole η₀ η₁ T q cost)
      (ξ : Measure (M × M)) (hξ : ξ ≤ πWhole)
      [MeasurableSpace (Option (Bool × T))]
      [MeasurableSingletonClass (Option (Bool × T))],
      let Refined := Cst.refineSubplan ξ hξ
      ∀ N : ℕ, ∀ᵐ sample ∂Refined.markedLaw N,
      ∀ ref, ∀ (classify : ℝ → Fin (Q ref).count),
      (∀ j s, s ∈ (Q ref).cell j → classify s = j) → ∀ (m n : ℕ) (selS : Fin m → Fin N) (selT : Fin n → Fin N)
      (hinjS : Injective selS) (hinjT : Injective selT),
      (∀ j, subplanRetentionFlag (sample.1 (selS j)).2 = false) →
      (∀ k, subplanRetentionFlag (sample.2 (selT k)).2 = false) →
      (∀ j, a (sample.1 (selS j)).1 ∈ C.roots ∩ U ref) →
      (∀ k, a (sample.2 (selT k)).1 ∈ C.roots ∩ U ref) →
      let cs := fun j ↦ classify (u (sample.1 (selS j)).1)
      let ct := fun k ↦ classify (u (sample.2 (selT k)).1)
      ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun
        (R (a (sample.2 (selT k)).1) - R (a (sample.1 (selS j)).1))
      let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
        C.clockClassAllowed (Q ref) (cs e.1) (ct e.2))
      let frozen := fun j k ↦ scale * C.clockClassKinetic (Q ref) ref.val (cs j) (ct k) (d j k)
      let modelProbe := fun j k ↦ C.clockClassProbe (Q ref) ref.val ref.property f (cs j) (ct k)
      ∀ σ : OTSelector.PartialMatching m n,
        PartialMatching.IsLegalOptimal allowed (fun j k ↦ frozen j k + tilt * modelProbe j k) σ →
        (∀ e ∈ (σ.embedIndices selS selT hinjS hinjT).edges,
          subplanRetentionFlag (sample.1 e.1).2 = false ∧
            subplanRetentionFlag (sample.2 e.2).2 = false) ∧
        (σ.embedIndices selS selT hinjS hinjT).cost (fun j k ↦
          scale * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
            u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1)) ≤
          (1 + (3 * ε + 2 * ε ^ 2)) *
            PartialMatching.legalMaximumValue allowed (fun j k ↦ frozen j k + tilt * modelProbe j k) +
          (PartialMatching.legalMaximumCard allowed : ℝ) *
            (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨Q, U, hU, houter, hforwardRegion, hgeometry, hcompetitor⟩ := D.exists_original_marked_every_clockClass_optimizer_with_forward_geometry
    hF hcomplete hu ha hinj horder hb hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1
    i f hgap hsep hη₀A hη₁B hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, houter, hforwardRegion, hgeometry, ?_⟩
  intro πWhole _ hπWhole T _ q cost Cst ξ hξ _ _
  let Refined := Cst.refineSubplan ξ hξ
  dsimp only
  intro N
  have hopt := hcompetitor πWhole hπWhole Cst ξ hξ N
  have hclock := D.original_marked_iid_core_clock_range_ae γ originalGap I hI.measurableSet hcomplete
    ha hu.continuous.measurable hlabel0 hlabel1 i hπWhole Refined.types (NS := Fin N) (NT := Fin N)
  filter_upwards [hopt, hclock] with sample hs hc
  intro ref classify hclass m n selS selT hinjS hinjT hflagS hflagT hrootS hrootT scale hscale tilt σ hσ
  exact hs ref m n selS selT hinjS hinjT
    (fun j ↦ classify (u (sample.1 (selS j)).1)) (fun k ↦ classify (u (sample.2 (selT k)).1))
    hflagS hflagT hrootS hrootT
    (fun j ↦ (Q ref).mem_classified_cell classify hclass (hc.1 (selS j) (hrootS j).1))
    (fun k ↦ (Q ref).mem_classified_cell classify hclass (hc.2 (selT k) (hrootT k).1))
    scale hscale tilt σ hσ

end OTSelector.Reconstruction
