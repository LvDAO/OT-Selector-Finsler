import OTSelector.Reconstruction.FinslerConcreteUpperClassGeometry

/-!
Every original retained root has an open self-neighborhood with actual Taylor,
coefficient and physical-probe control. These neighborhoods are chosen before
any reference-dependent finite class or Hall tolerance cover is selected.
-/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction.PopulationLocalPressureCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Full original clock bins and open neighborhoods can be chosen at every
reference before taking the finite Hall/class cover. Actual support points in
retained class edges satisfy the true distance/probe comparison with the
literal finite reference model. The same choices expose the original outer
clock endpoints and restore the Taylor region for every supported forward
pair, before any fine-class compatibility is known. -/
theorem exists_full_original_clockClass_geometry_with_forward_region (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M → ℝ) (hf : Continuous f)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobeError : 0 < probeError) :
    let C := D.haar.continuous.coefficient i
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ z₀, IsOpen (U z₀) ∧ z₀.val ∈ U z₀) ∧
      (∀ z₀ j k, C.clockClassAllowed (Q z₀) j k →
        ∀ s ∈ (Q z₀).cell j, ∀ t ∈ (Q z₀).cell k,
          s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1) ∧
      (∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
        ∀ s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
        ∀ t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
          s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
          (s, t) ∈ C.window.region) ∧
      ∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
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
          C.clockClassProbe (Q z₀) z₀.val z₀.property f j k| ≤ 2 * probeError := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨radius, hradius, hregion⟩ := D.exists_original_clock_region_radius hF i hgap hsep hscreen
  obtain ⟨U, hU, hgeometry⟩ := D.exists_original_pair_geometry_neighborhoods hF hcomplete hu ha hinj
    i f hf hε hprobeError hradius
  choose Q hQ using fun z₀ : C.roots ↦ C.exists_full_clockClass_model_with_endpoints
    hF hcomplete hu ha hinj z₀.val z₀.property f hf hI hglobalGap hε hprobeError
  refine ⟨Q, fun z₀ ↦ U z₀.val, fun z₀ ↦ hU z₀.val, ?_, ?_, ?_⟩
  · intro z₀ j k hjk s hs t ht
    exact ⟨(hQ z₀ j k hjk s hs t ht).1, (hQ z₀ j k hjk s hs t ht).2.1⟩
  · intro z₀ z hz z' hz' s hs t ht hst hA hB
    exact hregion z hz.1 z' hz'.1 s hs t ht
      (hgeometry z₀.val z₀.property z hz z' hz').1 hst hA hB
  intro z₀ z hz z' hz' j k hjk s hs t ht hA hB
  obtain ⟨hsI, htI, hhalf, hforward, hkin, hprobe⟩ := hQ z₀ j k hjk s hs t ht
  obtain ⟨hdiam, hcost, hphysicalProbe⟩ := hgeometry z₀.val z₀.property z hz z' hz'
  have hp := hregion z hz.1 z' hz'.1 s hsI t htI hdiam hforward hA hB
  refine ⟨hp, ?_, ?_⟩
  · let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
    let raw := matrixQuadratic (C.matrix z₀.val (s, t)) v
    let frozen := C.clockClassKinetic (Q z₀) z₀.val j k v
    have hraw_le : raw ≤ (1 + ε) * frozen := by
      have h := (abs_le.mp (hkin v)).2
      dsimp only [raw, frozen]
      linarith
    have hcost' := hcost (s, t) hp
    have hscaled := mul_le_mul_of_nonneg_left hraw_le (by positivity : 0 ≤ 2 * ε)
    have htri := abs_sub_le (populationSeedPairDeficit S (s, t) (R z, R z')) raw frozen
    have hbin := hkin v
    change |populationSeedPairDeficit S (s, t) (R z, R z') - frozen| ≤
      (3 * ε + 2 * ε ^ 2) * frozen
    nlinarith only [hcost', hscaled, htri, hbin]
  · have hreference : originalReferenceClockProbe C z₀.val z₀.property f (s, t) =
        f (D.corePoint i (z₀.val, s), D.corePoint i (z₀.val, t)) := by
      dsimp only [originalReferenceClockProbe, corePoint]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
        ⟨z₀.val, C.roots_subset_piece z₀.property⟩]
    have hphysical := hphysicalProbe s hsI t htI
    rw [← hreference] at hphysical
    have htri := abs_sub_le (f (D.corePoint i (z, s), D.corePoint i (z', t)))
      (originalReferenceClockProbe C z₀.val z₀.property f (s, t))
      (C.clockClassProbe (Q z₀) z₀.val z₀.property f j k)
    linarith


end OTSelector.Reconstruction.PopulationLocalPressureCore
