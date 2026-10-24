import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalPhysicalMean
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCardSum
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

/-- Every deterministic disjoint family of original retained cells receives
the physical expectation comparison on one common marked experiment. All
probe errors together spend at most the original N rows, uniformly over the
number of cells and over their dependent finite class sets. -/
theorem PopulationLocalPressureCore.exists_original_canonical_family_physical_expectation
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
      ∀ (J : Type*) [Fintype J] (reference : J → C.roots) (cell : J → Set (ℚ → M)),
      (∀ c, MeasurableSet (cell c)) → Pairwise (Disjoint on cell) →
      (∀ c, cell c ⊆ C.roots ∩ U (reference c)) →
      ∀ classify : ∀ c, ℝ → Fin (Q (reference c)).count,
      (∀ c, Measurable (classify c)) →
      (∀ c j x, x ∈ (Q (reference c)).cell j → classify c x = j) → ∀ (N : ℕ) (tilt : ℝ),
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let e := (Module.finBasis ℝ S.covector.ker).equivFunL
      let extra := fun c (cloud : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
        C.clockClassAllowed (Q (reference c)) (classify c (u (cloud.1 jk.1).1)) (classify c (u (cloud.2 jk.2).1)))
      let model := fun c (cloud : (Fin N → M × Option (Bool × T)) ×
          (Fin N → M × Option (Bool × T))) j k ↦
        (N : ℝ) ^ (2 / (q : ℝ)) * C.clockClassKinetic (Q (reference c)) (reference c).val
          (classify c (u (cloud.1 j).1)) (classify c (u (cloud.2 k).1))
          (e (R (a (cloud.2 k).1) - R (a (cloud.1 j).1))) +
        tilt * C.clockClassProbe (Q (reference c)) (reference c).val (reference c).property f
          (classify c (u (cloud.1 j).1)) (classify c (u (cloud.2 k).1))
      let σ := fun sample c ↦ originalRetainedCellOptimizer a cell extra model c sample
      let physical := fun sample ↦ ∑ c, (σ sample c).cost (fun j k ↦
        (N : ℝ) ^ (2 / (q : ℝ)) * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
          u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1))
      let frozen := fun sample ↦ ∑ c, (σ sample c).cost (model c sample)
      Integrable physical (Refined.markedLaw N) ∧ Integrable frozen (Refined.markedLaw N) ∧
        (∫ sample, physical sample ∂Refined.markedLaw N) ≤
          (1 + (3 * ε + 2 * ε ^ 2)) * (∫ sample, frozen sample ∂Refined.markedLaw N) +
          (N : ℝ) * (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) := by
  classical
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨Q, U, hU, houter, hregion, hgeometry, hcompare⟩ :=
    D.exists_original_canonical_cell_physical_expectation γ originalGap
      hF hcomplete hu ha hinj horder hb hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1
      i f hgap hsep hη₀A hη₁B hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, houter, hregion, hgeometry, ?_⟩
  intro πWhole _ hπWhole T _ Cst ξ hξ _ _
  let Refined := Cst.refineSubplan ξ hξ
  dsimp only
  intro J _ reference cell hcell hdisj hsub classify hm hclass N tilt
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let extra := fun c (cloud : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
    C.clockClassAllowed (Q (reference c)) (classify c (u (cloud.1 jk.1).1)) (classify c (u (cloud.2 jk.2).1)))
  let model := fun c (cloud : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) j k ↦
    (N : ℝ) ^ (2 / (q : ℝ)) * C.clockClassKinetic (Q (reference c)) (reference c).val
      (classify c (u (cloud.1 j).1)) (classify c (u (cloud.2 k).1))
      (e (R (a (cloud.2 k).1) - R (a (cloud.1 j).1))) +
    tilt * C.clockClassProbe (Q (reference c)) (reference c).val (reference c).property f
      (classify c (u (cloud.1 j).1)) (classify c (u (cloud.2 k).1))
  let σ := fun sample c ↦ originalRetainedCellOptimizer a cell extra model c sample
  let edge := fun (sample : (Fin N → M × Option (Bool × T)) × (Fin N → M × Option (Bool × T))) j k ↦
    (N : ℝ) ^ (2 / (q : ℝ)) * ((F.lengthEDist (sample.1 j).1 (sample.2 k).1).toReal -
      u (sample.2 k).1 + u (sample.1 j).1) + tilt * f ((sample.1 j).1, (sample.2 k).1)
  let physical := fun c sample ↦ (σ sample c).cost (edge sample)
  let frozen := fun c sample ↦ (σ sample c).cost (model c sample)
  let correction := |tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)
  have hlocal (c : J) : Integrable (physical c) (Refined.markedLaw N) ∧
      Integrable (frozen c) (Refined.markedLaw N) ∧
      Integrable (fun sample ↦ ((σ sample c).card : ℝ)) (Refined.markedLaw N) ∧
      (∫ sample, physical c sample ∂Refined.markedLaw N) ≤
        (1 + (3 * ε + 2 * ε ^ 2)) * (∫ sample, frozen c sample ∂Refined.markedLaw N) +
          (∫ sample, ((σ sample c).card : ℝ) ∂Refined.markedLaw N) * correction :=
    hcompare πWhole hπWhole Cst ξ hξ N (reference c) (classify c) (hm c) (hclass c)
      (cell c) (hcell c) (hsub c) tilt
  letI : IsProbabilityMeasure (Refined.markedLaw N) := (Refined.iid_facts hπWhole N).1
  have Iphysical := integrable_finsetSum Finset.univ (fun c _ ↦ (hlocal c).1)
  have Ifrozen := integrable_finsetSum Finset.univ (fun c _ ↦ (hlocal c).2.1)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ (hlocal c).2.2.2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hcard := integral_sum_card_originalRetainedCellOptimizer_le a cell hdisj extra model
    (Refined.markedLaw N) (fun c ↦ (hlocal c).2.2.1)
  have hcorrection : 0 ≤ correction := by dsimp only [correction]; positivity
  have hbound := hsum.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hcorrection))
  refine ⟨Iphysical, Ifrozen, ?_⟩
  calc
    _ = ∑ c, ∫ sample, physical c sample ∂Refined.markedLaw N :=
      integral_finsetSum Finset.univ (fun c _ ↦ (hlocal c).1)
    _ ≤ (1 + (3 * ε + 2 * ε ^ 2)) * (∑ c, ∫ sample, frozen c sample ∂Refined.markedLaw N) +
        (N : ℝ) * correction := hbound
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun c _ ↦ (hlocal c).2.1)]

end OTSelector.Reconstruction
