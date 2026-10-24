import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsReserveBounds
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsMargins

/-! Actual raw-prefix and deletion good counts produce every true block stage scalar floor. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal BigOperators ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Real finite law margins choose one fixed positive tolerance and scalar floor.
On one original-scene event, all actual original reserve arrays satisfying only
raw-grid prefix errors, total actual deletion errors and actual full-cut errors
produce nonnegative gammas and positive scalar floors in every positive block.
Endpoint backgrounds and protected first/last surviving counts are proved internally. -/
theorem OriginalSeedConditionalMoments.exists_actualClockBlock_stage_scalar_floors
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) {δ diameter : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ diameter)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    {θ : ℝ} (hθ : 0 < θ)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    : ∃ e : ℝ, 0 < e ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ R ell : ℝ,
    1 ≤ ell → 2*(originalStageFrameCollarFactor b*ell) ≤ R →
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ),
      let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
      (∀ block, Cs block ⊆ G.sourceBlockCell μ ν block) →
      (∀ block, Ct block ⊆ G.targetBlockCell μ ν block) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
          originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs block)) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
          originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct block)) →
      (∀ k : Fin (G.count+1),
        |(originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Ico (G.cut 0) (G.cut k.val)) : ℝ) -
          θ*A.cubeVolume*μ.real (Ico (G.cut 0) (G.cut k.val))| ≤ e*A.cubeVolume) →
      (∀ k : Fin (G.count+1),
        |(originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ioc (G.cut 0) (G.cut k.val)) : ℝ) -
          θ*A.cubeVolume*ν.real (Ioc (G.cut 0) (G.cut k.val))| ≤ e*A.cubeVolume) →
      (((∑ block : G.ClockSlabBlock μ ν,
        (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
          (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
            ((scene,target),source.1,fun i ↦ (source.2 i).2) +
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
          (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
            ((scene,source),target.1,fun i ↦ (target.2 i).2))) : ℕ) : ℝ) ≤ e*A.cubeVolume →
      (∀ k : Fin (G.count+1), |originalOrientedStageFullCutError S w b R (G.cut k.val) scene| ≤ e*A.cubeVolume) →
      ∀ block : G.ClockSlabBlock μ ν, block ∈ G.positiveSlabBlocks μ ν →
        A.gamma (G.cut block.lower.val) = 0 ∧ A.gamma (G.cut block.upper.val) = 0 ∧
        A.orientedBackgroundLaw (G.cut block.lower.val) = 0 ∧ A.orientedBackgroundLaw (G.cut block.upper.val) = 0 ∧
        (∀ k : Fin (G.count+1), block.lower ≤ k → k ≤ block.upper → 0 ≤ A.gamma (G.cut k.val)) ∧
        ∀ i : Fin G.count, block.Contains i →
          ρ ≤ A.gamma (G.cut i.val) +
            (originalStageRemainingReserveClassCount source A.sourceKept (G.sourceCell i) : ℝ)/A.cubeVolume ∧
          ρ ≤ A.gamma (G.cut (i.val+1)) +
            (originalStageRemainingReserveClassCount target A.targetKept (G.targetCell i) : ℝ)/A.cubeVolume := by
  have : IsProbabilityMeasure μ := D.support.source.probability
  have : IsProbabilityMeasure ν := D.support.target.probability
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  let π := η.map Prod.fst
  have : IsProbabilityMeasure η := Q.palm_probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · simpa only [π,η,Measure.map_map measurable_fst measurable_fst,Function.comp_def] using Q.source_clock
    · simpa only [π,η,Measure.map_map measurable_snd measurable_fst,Function.comp_def] using Q.target_clock
  have hweak : ∀ᵐ p ∂π, p.1 ≤ p.2 :=
    (ae_map_iff measurable_fst.aemeasurable (measurableSet_le measurable_fst measurable_snd)).mpr
      (Q.ae_palm_forward.mono fun _ hp ↦ hp.le)
  obtain ⟨h₀,hN,hH⟩ := G.clockSlabSurplus_facts hδ hsep π hπ hs ht hmono hweak
  obtain ⟨e,he,ρ,hρ,hmargins⟩ := G.exists_positiveBlock_error_and_floor hmono hH hθ
  refine ⟨e,he,ρ,hρ,?_⟩
  intro R ell hell hR
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hgammas := ae_all_iff.mpr (fun k : Fin (G.count+1) ↦
    D.ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError hF hw Q b hell hR hRone (G.cut k.val))
  filter_upwards [D.ae_all_originalOrientedClockBlockKeptEndpoints_zero hF hw Q G hδ hsep hs ht hmono b hell hR,
    hgammas] with scene hzero hgamma
  intro source target Cs Ct
  dsimp only
  let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
  intro hCs hCt hsCap htCap hpreS hpreT hdel hcut
  have hends := hzero source target Cs Ct hCs hCt hsCap htCap
  have hres := originalOrientedClockBlockKeptData_reserve_bounds (S := S) (w := w)
    G h₀ hN b R ell θ e scene source target Cs Ct hpreS hpreT hdel
  have hV : 0 < A.cubeVolume := A.cubeVolume_pos (by linarith)
  have hgammaLower (k : Fin (G.count+1)) : θ*G.clockSlabSurplus μ ν k.val-4*e ≤ A.gamma (G.cut k.val) := by
    have hc := hgamma k source target A.sourceKept A.targetKept
    change A.gamma (G.cut k.val) = (A.reservePrefix (G.cut k.val)+
      originalOrientedStageFullCutError S w b R (G.cut k.val) scene)/A.cubeVolume at hc
    rw [hc]
    apply (le_div_iff₀ hV).mpr
    have hr := hres.1 k
    have hd := (abs_le.mp (hcut k)).1
    nlinarith only [hr,hd]
  intro block hb
  have hm := hmargins block hb
  have hinner (k : Fin (G.count+1)) (hl : block.lower < k) (hu : k < block.upper) :
      ρ ≤ A.gamma (G.cut k.val) := (hm.2.2 k hl hu).trans (hgammaLower k)
  have hlow := (hends.1 block.lower block.consecutive.2.1).1
  have hupp := (hends.1 block.upper block.consecutive.2.2.1).1
  have hnonneg (k : Fin (G.count+1)) (hl : block.lower ≤ k) (hu : k ≤ block.upper) :
      0 ≤ A.gamma (G.cut k.val) := by
    by_cases heq : k = block.lower
    · subst k
      exact hlow.symm.le
    by_cases heq' : k = block.upper
    · subst k
      exact hupp.symm.le
    exact hρ.le.trans (hinner k (lt_of_le_of_ne hl (Ne.symm heq)) (lt_of_le_of_ne hu heq'))
  refine ⟨hlow,hupp,(hends.2 block).1,(hends.2 block).2,hnonneg,?_⟩
  intro i hi
  let kl : Fin (G.count+1) := ⟨i.val,by omega⟩
  let kr : Fin (G.count+1) := ⟨i.val+1,by omega⟩
  have hsl : θ*μ.real (G.sourceCell i)-3*e ≤
      (originalStageRemainingReserveClassCount source A.sourceKept (G.sourceCell i) : ℝ)/A.cubeVolume := by
    apply (le_div_iff₀ hV).mpr
    nlinarith only [(hres.2 i).1]
  have htl : θ*ν.real (G.targetCell i)-3*e ≤
      (originalStageRemainingReserveClassCount target A.targetKept (G.targetCell i) : ℝ)/A.cubeVolume := by
    apply (le_div_iff₀ hV).mpr
    nlinarith only [(hres.2 i).2]
  constructor
  · by_cases heq : i.val = block.lower.val
    · have hif : i = G.firstBlockClass block := Fin.ext heq
      have hh : ρ ≤ θ*μ.real (G.sourceCell i)-3*e := by simpa only [hif] using hm.1
      have hz : A.gamma (G.cut i.val) = 0 := by rw [heq]; exact hlow
      linarith only [hh,hsl,hz]
    · have hh := hinner kl (by change block.lower.val < i.val; have h := hi.1; omega) hi.2
      have hn : 0 ≤ (originalStageRemainingReserveClassCount source A.sourceKept (G.sourceCell i) : ℝ)/A.cubeVolume :=
        div_nonneg (Nat.cast_nonneg _) hV.le
      linarith only [hh,hn]
  · by_cases heq : i.val+1 = block.upper.val
    · have hil : i = G.lastBlockClass block := Fin.ext (by change i.val = block.upper.val-1; omega)
      have hh : ρ ≤ θ*ν.real (G.targetCell i)-3*e := by simpa only [hil] using hm.2.1
      have hz : A.gamma (G.cut (i.val+1)) = 0 := by rw [heq]; exact hupp
      linarith only [hh,htl,hz]
    · have hh := hinner kr (by change block.lower.val < i.val+1; have h := hi.1; omega)
        (by change i.val+1 < block.upper.val; have h := hi.2; omega)
      have hn : 0 ≤ (originalStageRemainingReserveClassCount target A.targetKept (G.targetCell i) : ℝ)/A.cubeVolume :=
        div_nonneg (Nat.cast_nonneg _) hV.le
      linarith only [hh,hn]

end OTSelector.Reconstruction
