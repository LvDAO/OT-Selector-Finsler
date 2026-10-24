import OTSelector.Reconstruction.FinslerRelativeLawActualCorePointSampling
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergy
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

/-- The actual legal finite class competitor embeds in the unchanged original
marked iid arrays. Original endpoint recovery and original support hypotheses
discharge all seed-position premises of the geometric competitor. -/
theorem PopulationLocalPressureCore.exists_original_marked_clockClass_competitors
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

    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ y ∂η₁, y ∈ B)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobeError : 0 < probeError)
    {πWhole : Measure (M × M)} [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    {T : Type*} [Fintype T] {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T q cost)
    (ξ : Measure (M × M)) (hξ : ξ ≤ πWhole)
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))] :
    let C := D.haar.continuous.coefficient i
    let Refined := Cst.refineSubplan ξ hξ
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ ref, IsOpen (U ref) ∧ ref.val ∈ U ref) ∧
      ∀ N : ℕ, ∀ᵐ sample ∂Refined.markedLaw N,
      ∀ ref, ∀ (m n : ℕ) (selS : Fin m → Fin N) (selT : Fin n → Fin N)
      (hinjS : Injective selS) (hinjT : Injective selT)
      (cs : Fin m → Fin (Q ref).count) (ct : Fin n → Fin (Q ref).count),
      (∀ j, subplanRetentionFlag (sample.1 (selS j)).2 = false) →
      (∀ k, subplanRetentionFlag (sample.2 (selT k)).2 = false) →
      (∀ j, a (sample.1 (selS j)).1 ∈ C.roots ∩ U ref) →
      (∀ k, a (sample.2 (selT k)).1 ∈ C.roots ∩ U ref) →
      (∀ j, u (sample.1 (selS j)).1 ∈ (Q ref).cell (cs j)) →
      (∀ k, u (sample.2 (selT k)).1 ∈ (Q ref).cell (ct k)) →
      ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun
        (R (a (sample.2 (selT k)).1) - R (a (sample.1 (selS j)).1))
      let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
        C.clockClassAllowed (Q ref) (cs e.1) (ct e.2))
      let frozen := fun j k ↦ scale * C.clockClassKinetic (Q ref) ref.val (cs j) (ct k) (d j k)
      let modelProbe := fun j k ↦ C.clockClassProbe (Q ref) ref.val ref.property f (cs j) (ct k)
      ∃ σ : OTSelector.PartialMatching m n,
        PartialMatching.IsLegal allowed σ ∧ σ.card = PartialMatching.legalMaximumCard allowed ∧
        σ.cost (fun j k ↦ frozen j k + tilt * modelProbe j k) =
          PartialMatching.legalMaximumValue allowed (fun j k ↦ frozen j k + tilt * modelProbe j k) ∧
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
  let Refined := Cst.refineSubplan ξ hξ
  obtain ⟨Q, U, hU, hcompetitor⟩ := D.exists_original_clockClass_partial_competitors
    hF hcomplete hu ha hinj i f hgap hsep hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, ?_⟩
  intro N
  have hpoints := D.original_marked_iid_cell_corePoint_ae hF hcomplete hu ha hinj horder hb
    hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1 i C.roots_compact.measurableSet
    (Subset.refl C.roots) hπWhole Refined.types (NS := Fin N) (NT := Fin N)
  have hsA : ∀ᵐ x ∂Measure.pi (fun _ : Fin N ↦ η₀), ∀ j, x j ∈ A :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ η₀) j).ae hη₀A
  have htB : ∀ᵐ y ∂Measure.pi (fun _ : Fin N ↦ η₁), ∀ k, y k ∈ B :=
    ae_all_iff.mpr fun k ↦ (Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ η₁) k).ae hη₁B
  have hcarriers : ∀ᵐ sample ∂Refined.markedLaw N,
      (∀ j, (sample.1 j).1 ∈ A) ∧ (∀ k, (sample.2 k).1 ∈ B) := by
    apply Refined.types.iid_original_physical_property (I := Fin N) (J := Fin N) hπWhole
      (fun sample : (Fin N → M) × (Fin N → M) ↦
        (∀ j, sample.1 j ∈ A) ∧ (∀ k, sample.2 k ∈ B))
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsA,
      Measure.quasiMeasurePreserving_snd.ae htB] with sample hs ht
    exact ⟨hs, ht⟩
  filter_upwards [hpoints, hcarriers] with sample hp hc
  intro ref m n selS selT hinjS hinjT cs ct hflagS hflagT hrootS hrootT hclockS hclockT scale hscale tilt
  have hsource (j : Fin m) : D.corePoint i (a (sample.1 (selS j)).1, u (sample.1 (selS j)).1) =
      (sample.1 (selS j)).1 := hp.1 (selS j) (hrootS j).1
  have htarget (k : Fin n) : D.corePoint i (a (sample.2 (selT k)).1, u (sample.2 (selT k)).1) =
      (sample.2 (selT k)).1 := hp.2 (selT k) (hrootT k).1
  obtain ⟨σ, hlegal, hcard, hmodel, hbound⟩ := hcompetitor ref m n
    (fun j ↦ a (sample.1 (selS j)).1) (fun k ↦ a (sample.2 (selT k)).1) cs ct
    (fun j ↦ u (sample.1 (selS j)).1) (fun k ↦ u (sample.2 (selT k)).1)
    hrootS hrootT hclockS hclockT
    (fun j ↦ (hsource j).symm ▸ hc.1 (selS j)) (fun k ↦ (htarget k).symm ▸ hc.2 (selT k))
    scale hscale tilt
  refine ⟨σ, hlegal, hcard, hmodel, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hflagS p.1, hflagT p.2⟩
  · rw [OTSelector.PartialMatching.cost_embedIndices]
    have hcost : (fun j k ↦ scale * populationSeedPairDeficit (P C.seedIndex).seed
        (u (sample.1 (selS j)).1, u (sample.2 (selT k)).1)
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (sample.1 (selS j)).1),
          populationSeedRootLabelValue (P C.seedIndex).seed a (a (sample.2 (selT k)).1)) +
        tilt * f (D.corePoint i (a (sample.1 (selS j)).1, u (sample.1 (selS j)).1),
          D.corePoint i (a (sample.2 (selT k)).1, u (sample.2 (selT k)).1))) =
      (fun j k ↦ scale * ((F.lengthEDist (sample.1 (selS j)).1 (sample.2 (selT k)).1).toReal -
        u (sample.2 (selT k)).1 + u (sample.1 (selS j)).1) +
          tilt * f ((sample.1 (selS j)).1, (sample.2 (selT k)).1)) := by
      funext j k
      have hs := hsource j
      have ht := htarget k
      dsimp only [PopulationLocalPressureCore.corePoint] at hs ht
      dsimp only [populationSeedPairDeficit]
      rw [hs, ht, hsource, htarget]
    dsimp only at hbound ⊢
    rw [hcost] at hbound
    exact hbound

end OTSelector.Reconstruction
