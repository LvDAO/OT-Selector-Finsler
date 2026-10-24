import OTSelector.Geometry.Finsler.Calibration.SeedPhysicalMap
import OTSelector.Reconstruction.FinslerPopulationHaarPressureCore

/-!
# Geometry.Finsler.Calibration.SeedPhysicalMap

* **Conditions:** An actual complete calibrated seed curve with its Borel label subtype.
* **Objects:** A globally measurable physical label–clock map agreeing with that same complete curve at every actual seed label.
* **Proof detail:** Extend the time-shifted actual seed map from the measurable subtype embedding and evaluate it on that image.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (adapter): The selected three commands define/read the actual physical map; statements identifying supplied conditional inverses are outside this extraction.
-/

/-!
# The original physical inverse is the actual complete seed curve

The stored common calibrated support span identifies the original inverse of the
label-clock map with the same complete seed curve under both original conditional
laws. This supplies the physical positions for the retained Haar-clock populations.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- At every actual active time the original label-clock inverse is exactly the
same complete seed curve, with its original potential offset. -/
theorem seed_curve_eq_original_inverse_on_active
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedInverseMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _instSeedInverseOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {b : Z × ℝ → M}
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {t : ℝ} (ht : t ∈ interior (S.calibrationTimes w)) :
    b (a (S.curve w 0), S.level + t) = S.curve w t := by
  have hwin := ht
  rw [← S.iUnion_rationalWindow_timeDomain hF hu hw] at hwin
  obtain ⟨k, hk⟩ := mem_iUnion.mp hwin
  have hreg := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
    ((S.rationalWindow k).mapsTo_calibratedInterior hF hu hk)
  have hlabel := (S.rationalWindow k).label_toManifold_eq_initial
    hF hcomplete hu horder hk
  have hclock : u (S.curve w t) = S.level + t := by
    change t ∈ S.calibrationTimes w
    exact interior_subset ht
  have h := hinv _ hreg
  change b (a (S.curve w t), u (S.curve w t)) = S.curve w t at h
  change a (S.curve w t) = a (S.curve w 0) at hlabel
  rwa [hlabel, hclock] at h

omit [BorelSpace E] in
/-- The actual common calibrated span identifies the physical inverse for both
original scalar conditional laws, including densities that vanish inside the span. -/
theorem CommonSeedSupportSpan.original_inverse_ae
    {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker}
    {μ ν : Measure ℝ} {lo hi : ℝ} (D : CommonSeedSupportSpan S w μ ν lo hi)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSpanInverseMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _instSpanInverseOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {b : Z × ℝ → M}
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hw : w ∈ S.labels) :
    (∀ᵐ x ∂μ, b (a (S.curve w 0), x) = S.curve w (x - S.level)) ∧
      (∀ᵐ x ∂ν, b (a (S.curve w 0), x) = S.curve w (x - S.level)) := by
  have hactive : Ioo lo hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.calibrated
  have hpoint (x : ℝ) (hx : x - S.level ∈ Ioo lo hi) :
      b (a (S.curve w 0), x) = S.curve w (x - S.level) := by
    simpa only [add_sub_cancel] using seed_curve_eq_original_inverse_on_active
      S hF hcomplete hu horder hinv hw (hactive hx)
  exact ⟨D.source.ae_open.mono hpoint, D.target.ae_open.mono hpoint⟩

variable [MeasurableSpace M] [BorelSpace M]





/-- On every retained actual pressure root, the two original conditional laws read
the same complete physical seed curve through the original inverse map. -/
theorem PopulationHaarPressureCore.original_inverse_ae
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHaarInverseMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instHaarInverseOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (i : Fin D.continuous.count) {z : ℚ → M} (hz : z ∈ (D.continuous.coefficient i).roots) :
    let S := (P (D.continuous.coefficient i).seedIndex).seed
    let w := populationSeedRootLabelValue S a z
    (∀ᵐ t ∂condDistrib u a η₀ z, b (z, t) = S.curve w (t - S.level)) ∧
      (∀ᵐ t ∂condDistrib u a η₁ z, b (z, t) = S.curve w (t - S.level)) := by
  let _instHaarInverseMetric : MetricSpace M := F.metricSpace
  let _instHaarInverseProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instHaarInversePolish : PolishSpace M := inferInstance
  let _instHaarInverseBorel : BorelSpace (ℚ → M) := inferInstance
  let j := (D.continuous.coefficient i).seedIndex
  have hzpiece := (D.continuous.coefficient i).roots_subset_piece hz
  have hzpop : z ∈ D.continuous.population.roots :=
    D.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  obtain ⟨W⟩ := ((D.continuous.population.good z hzpop).2 j hzpiece).1
  have h := W.support.original_inverse_ae hF hcomplete hu horder hinv
    (populationSeedPieceLabel P a κ lambda j ⟨z, hzpiece⟩).property
  rw [populationSeedPieceLabel_root P a κ lambda j ⟨z, hzpiece⟩] at h
  dsimp only
  rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hzpiece⟩]
  exact h

/-- The exact Haar-clock joint law reconstructs the original physical restriction
through the actual complete seed positions. -/
theorem original_seed_core_physical_recovery_of_joint
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedPhysicalMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (η : Measure M) [IsFiniteMeasure η] {b : Z × ℝ → M} (hb : Measurable b)
    (hηinv : ∀ᵐ x ∂η, b (a x, u x) = x)
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (hjoint : (η.restrict (a ⁻¹' K)).map (fun x ↦ (a x, u x)) =
      lambda.restrict K ⊗ₘ condDistrib u a η)
    (hcurve : ∀ z ∈ K, ∀ᵐ t ∂condDistrib u a η z,
      b (z, t) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z)
        (t - (P j).seed.level)) :
    ((((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda j)) ⊗ₘ
        populationSeedCoordinateClockKernel (P j).seed a ha (condDistrib u a η)).map
          (populationSeedPhysicalMap (P j).seed) = η.restrict (a ⁻¹' K) := by
  let _instSeedPhysicalMetric : MetricSpace M := F.metricSpace
  let _instSeedPhysicalProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSeedPhysicalPolish : PolishSpace M := inferInstance
  let R := populationSeedRootLabelValue (P j).seed a
  have hR := measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  have hphysical := measurable_populationSeedPhysicalMap (P j).seed
  have hmeas : Measurable (fun q : Z × ℝ ↦
      populationSeedPhysicalMap (P j).seed (R q.1, q.2)) :=
    hphysical.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hpair : ∀ᵐ q ∂lambda.restrict K ⊗ₘ condDistrib u a η,
      populationSeedPhysicalMap (P j).seed (R q.1, q.2) = b q := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hmeas hb)
    filter_upwards [ae_restrict_mem hK] with z hz
    filter_upwards [hcurve z hz] with t ht
    rw [ht]
    dsimp only [R]
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hsub hz⟩,
      populationSeedPhysicalMap_at_label]
  have hphysicalAE : ∀ᵐ x ∂η.restrict (a ⁻¹' K),
      populationSeedPhysicalMap (P j).seed (R (a x), u x) = b (a x, u x) := by
    exact ae_of_ae_map
      (p := fun q : Z × ℝ ↦ populationSeedPhysicalMap (P j).seed (R q.1, q.2) = b q)
      (ha.prodMk hu.continuous.measurable).aemeasurable (by rw [hjoint]; exact hpair)
  have hQ : Measurable (fun x ↦ (populationSeedRootLabelValue (P j).seed a (a x), u x)) :=
    (hR.comp ha).prodMk hu.continuous.measurable
  rw [← original_seed_core_joint_eq_compProd_of_joint P a κ lambda
    hF hcomplete hu ha hinj η j hK hsub hjoint,
    Measure.map_map hphysical hQ]
  calc
    _ = (η.restrict (a ⁻¹' K)).map id := by
      apply Measure.map_congr
      filter_upwards [hphysicalAE, ae_restrict_of_ae hηinv] with x hx hi
      exact hx.trans hi
    _ = _ := Measure.map_id

/-- Every original physical sample whose root is retained in a finite pressure
piece is the actual complete seed position at its original potential clock. -/
theorem PopulationHaarPressureCore.physical_endpoints_ae
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPhysicalEndpointsMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPhysicalEndpointsOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u) :
    (∀ᵐ x ∂η₀, ∀ i : Fin D.continuous.count,
      a x ∈ (D.continuous.coefficient i).roots →
      let S := (P (D.continuous.coefficient i).seedIndex).seed
      x = S.curve (populationSeedRootLabelValue S a (a x)) (u x - S.level)) ∧
    (∀ᵐ x ∂η₁, ∀ i : Fin D.continuous.count,
      a x ∈ (D.continuous.coefficient i).roots →
      let S := (P (D.continuous.coefficient i).seedIndex).seed
      x = S.curve (populationSeedRootLabelValue S a (a x)) (u x - S.level)) := by
  let _instPhysicalEndpointsMetric : MetricSpace M := F.metricSpace
  let _instPhysicalEndpointsProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPhysicalEndpointsPolish : PolishSpace M := inferInstance
  let _instPhysicalEndpointsBorel : BorelSpace (ℚ → M) := inferInstance
  have hcolor (η : Measure M) [IsFiniteMeasure η]
      (hreg : ∀ᵐ x ∂η, x ∈ F.potentialRegularDomain u)
      (hjoint : ∀ i, (η.restrict (a ⁻¹' (D.continuous.coefficient i).roots)).map
          (fun x ↦ (a x, u x)) =
          lambda.restrict (D.continuous.coefficient i).roots ⊗ₘ condDistrib u a η)
      (hcurve : ∀ i, ∀ z ∈ (D.continuous.coefficient i).roots,
        let S := (P (D.continuous.coefficient i).seedIndex).seed
        ∀ᵐ t ∂condDistrib u a η z,
          b (z, t) = S.curve (populationSeedRootLabelValue S a z) (t - S.level)) :
      ∀ᵐ x ∂η, ∀ i : Fin D.continuous.count,
        a x ∈ (D.continuous.coefficient i).roots →
        let S := (P (D.continuous.coefficient i).seedIndex).seed
        x = S.curve (populationSeedRootLabelValue S a (a x)) (u x - S.level) := by
    rw [ae_all_iff]
    intro i
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    have hR := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
    have hmeas : Measurable (fun q : (ℚ → M) × ℝ ↦
        populationSeedPhysicalMap S (R q.1, q.2)) :=
      (measurable_populationSeedPhysicalMap S).comp
        ((hR.comp measurable_fst).prodMk measurable_snd)
    have hmap (z) (hz : z ∈ C.roots) (t : ℝ) :
        populationSeedPhysicalMap S (R z, t) = S.curve (R z) (t - S.level) := by
      dsimp only [R, S]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
        ⟨z, C.roots_subset_piece hz⟩, populationSeedPhysicalMap_at_label]
    have hpair : ∀ᵐ q ∂lambda.restrict C.roots ⊗ₘ condDistrib u a η,
        populationSeedPhysicalMap S (R q.1, q.2) = b q := by
      apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hmeas hb)
      filter_upwards [ae_restrict_mem (D.continuous.recovery.measurable i)] with z hz
      filter_upwards [hcurve i z hz] with t ht
      exact (hmap z hz t).trans ht.symm
    have hphysical : ∀ᵐ x ∂η.restrict (a ⁻¹' C.roots),
        populationSeedPhysicalMap S (R (a x), u x) = b (a x, u x) :=
      ae_of_ae_map
        (p := fun q : (ℚ → M) × ℝ ↦ populationSeedPhysicalMap S (R q.1, q.2) = b q)
        (ha.prodMk hu.continuous.measurable).aemeasurable
        (by rw [hjoint i]; exact hpair)
    apply ae_imp_of_ae_restrict
    filter_upwards [hphysical, ae_restrict_of_ae hreg,
      ae_restrict_mem (ha (D.continuous.recovery.measurable i))] with x hx hxreg hxroot
    exact (hinv x hxreg).symm.trans (hx.symm.trans (hmap (a x) hxroot (u x)))
  exact ⟨hcolor η₀ hη₀reg D.continuous.recovery.source_joint
      (fun i z hz ↦ (D.original_inverse_ae hF hcomplete hu ha hinj horder hinv i hz).1),
    hcolor η₁ hη₁reg D.continuous.recovery.target_joint
      (fun i z hz ↦ (D.original_inverse_ae hF hcomplete hu ha hinj horder hinv i hz).2)⟩

section Recovery

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
  (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instPhysicalRecoveryMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _instPhysicalRecoveryOrder : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hb : Measurable b)
  (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
  (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
  (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)

include hF hcomplete hu hinj horder hb hinv hη₀reg hη₁reg

/-- Each retained original Haar-clock population reconstructs its physical color
through the actual complete seed curve, using the original atlas data alone. -/
theorem PopulationHaarPressureCore.physical_piece_laws
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let intensity := ((κ C.seedIndex).restrict (R '' C.roots)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    (intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha
      (condDistrib u a η₀)).map (populationSeedPhysicalMap S) =
        η₀.restrict (a ⁻¹' C.roots) ∧
    (intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha
      (condDistrib u a η₁)).map (populationSeedPhysicalMap S) =
        η₁.restrict (a ⁻¹' C.roots) := by
  let _instPhysicalRecoveryMetric : MetricSpace M := F.metricSpace
  let _instPhysicalRecoveryProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPhysicalRecoveryPolish : PolishSpace M := inferInstance
  let _instPhysicalRecoveryBorel : BorelSpace (ℚ → M) := inferInstance
  exact ⟨original_seed_core_physical_recovery_of_joint P a κ lambda
      hF hcomplete hu ha hinj η₀ hb (hη₀reg.mono fun x hx ↦ hinv x hx)
      (D.continuous.coefficient i).seedIndex (D.continuous.recovery.measurable i)
      (D.continuous.coefficient i).roots_subset_piece
      (D.continuous.recovery.source_joint i)
      (fun z hz ↦ (D.original_inverse_ae hF hcomplete hu ha hinj horder hinv i hz).1),
    original_seed_core_physical_recovery_of_joint P a κ lambda
      hF hcomplete hu ha hinj η₁ hb (hη₁reg.mono fun x hx ↦ hinv x hx)
      (D.continuous.coefficient i).seedIndex (D.continuous.recovery.measurable i)
      (D.continuous.coefficient i).roots_subset_piece
      (D.continuous.recovery.target_joint i)
      (fun z hz ↦ (D.original_inverse_ae hF hcomplete hu ha hinj horder hinv i hz).2)⟩

/-- The finite actual Haar-clock populations and the original complementary
physical restrictions recover both original laws with their original masses. -/
theorem PopulationHaarPressureCore.physical_recovery :
    let physical (η : Measure M) [IsFiniteMeasure η] (i : Fin D.continuous.count) :=
      let C := D.continuous.coefficient i
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      ((((κ C.seedIndex).restrict (R '' C.roots)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)) ⊗ₘ
          populationSeedCoordinateClockKernel S a ha (condDistrib u a η)).map
            (populationSeedPhysicalMap S)
    (∑ i, physical η₀ i) +
      η₀.restrict (a ⁻¹' (⋃ i, (D.continuous.coefficient i).roots)ᶜ) = η₀ ∧
    (∑ i, physical η₁ i) +
      η₁.restrict (a ⁻¹' (⋃ i, (D.continuous.coefficient i).roots)ᶜ) = η₁ := by
  have hp := D.physical_piece_laws hF hcomplete hu ha hinj horder hb hinv hη₀reg hη₁reg
  dsimp only
  constructor
  · simp_rw [fun i ↦ (hp i).1]
    exact D.continuous.recovery.source_decomposition
  · simp_rw [fun i ↦ (hp i).2]
    exact D.continuous.recovery.target_decomposition

end Recovery
end OTSelector.Reconstruction
