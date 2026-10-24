import OTSelector.Reconstruction.FinslerRelativeLawOriginalClassifiedForwardRegion
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

/-- The measurable canonical optimizer on each literal original retained
cell satisfies the actual physical upper comparison. Original clock-bin
membership, seed endpoint recovery, complete enumeration and optimizer
restriction are all discharged internally; geometry is chosen before every
rebuilt original coupling and residual experiment. -/
theorem PopulationLocalPressureCore.exists_original_canonical_cell_physical_comparison_with_forward_region
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
      (∀ j s, s ∈ (Q ref).cell j → classify s = j) →
      ∀ L : Set (ℚ → M), L ⊆ C.roots ∩ U ref → ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.1
      let g := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.2
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let extra := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun p : Fin N × Fin N ↦
        C.clockClassAllowed (Q ref) (classify (u (sample.1 p.1).1)) (classify (u (sample.2 p.2).1)))
      let model := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) j k ↦
        scale * C.clockClassKinetic (Q ref) ref.val
          (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
          ((Module.finBasis ℝ S.covector.ker).equivFun (R (a (sample.2 k).1) - R (a (sample.1 j).1))) +
        tilt * C.clockClassProbe (Q ref) ref.val ref.property f
          (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
      let σ := originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra model () sample
      σ.cost (fun j k ↦ scale * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
          u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1)) ≤
        (1 + (3 * ε + 2 * ε ^ 2)) *
          PartialMatching.legalMaximumValue (PartialMatching.inducedLegalGraph (extra () sample) e g)
            (fun j k ↦ model () sample (e j) (g k)) +
        (PartialMatching.legalMaximumCard (PartialMatching.inducedLegalGraph (extra () sample) e g) : ℝ) *
          (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨Q, U, hU, houter, hforwardRegion, hcomparison⟩ := D.exists_original_marked_classified_clockClass_optimizers_with_forward_region γ originalGap
    hF hcomplete hu ha hinj horder hb hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1
    i f hgap hsep hη₀A hη₁B hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, houter, hforwardRegion, ?_⟩
  intro πWhole _ hπWhole T _ q cost Cst ξ hξ _ _
  let Refined := Cst.refineSubplan ξ hξ
  dsimp only
  intro N
  filter_upwards [hcomparison πWhole hπWhole Cst ξ hξ N] with sample hs
  intro ref classify hclass L hL scale hscale tilt
  let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.1
  let g := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' L)) sample.2
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let extra := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun p : Fin N × Fin N ↦
    C.clockClassAllowed (Q ref) (classify (u (sample.1 p.1).1)) (classify (u (sample.2 p.2).1)))
  let model := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) j k ↦
    scale * C.clockClassKinetic (Q ref) ref.val
      (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
      ((Module.finBasis ℝ S.covector.ker).equivFun (R (a (sample.2 k).1) - R (a (sample.1 j).1))) +
    tilt * C.clockClassProbe (Q ref) ref.val ref.property f
      (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
  let σ := originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra model () sample
  have he (j) : subplanRetentionFlag (sample.1 (e j)).2 = false ∧ a (sample.1 (e j)).1 ∈ L :=
    (finiteOriginalRestrictedEmbedding_range _ _ _).mp ⟨j, rfl⟩
  have hg (k) : subplanRetentionFlag (sample.2 (g k)).2 = false ∧ a (sample.2 (g k)).1 ∈ L :=
    (finiteOriginalRestrictedEmbedding_range _ _ _).mp ⟨k, rfl⟩
  have hgraph : PartialMatching.inducedLegalGraph (extra () sample) e g =
      Finset.univ.filter (fun p ↦ C.clockClassAllowed (Q ref)
        (classify (u (sample.1 (e p.1)).1)) (classify (u (sample.2 (g p.2)).1))) := by
    ext p
    simp [PartialMatching.inducedLegalGraph, extra]
  have hopt := originalRetainedCellOptimizer_prefix_isLegalOptimal a (fun _ : Unit ↦ L) extra model () sample
  change PartialMatching.IsLegalOptimal (PartialMatching.inducedLegalGraph (extra () sample) e g)
    (fun j k ↦ model () sample (e j) (g k)) (σ.comapEmbedding e g) at hopt
  rw [hgraph] at hopt
  have hb := (hs ref classify hclass _ _ e g e.injective g.injective
    (fun j ↦ (he j).1) (fun k ↦ (hg k).1)
    (fun j ↦ hL (he j).2) (fun k ↦ hL (hg k).2)
    scale hscale tilt (σ.comapEmbedding e g) hopt).2
  have hcost := originalRetainedCellOptimizer_prefix_embedded_cost_eq a (fun _ : Unit ↦ L) extra model () sample
    (fun j k ↦ scale * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
      u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1))
  rw [hcost] at hb
  change σ.cost (fun j k ↦ scale * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
      u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1)) ≤
    (1 + (3 * ε + 2 * ε ^ 2)) *
      PartialMatching.legalMaximumValue (PartialMatching.inducedLegalGraph (extra () sample) e g)
        (fun j k ↦ model () sample (e j) (g k)) +
    (PartialMatching.legalMaximumCard (PartialMatching.inducedLegalGraph (extra () sample) e g) : ℝ) *
      (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
  rw [hgraph]
  exact hb

end OTSelector.Reconstruction
