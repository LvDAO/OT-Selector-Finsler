import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicLabelGeometry
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Actual macroscopic isolation inside the retained finite union of original cores

The one fixed seed frame separates the selected compact label core from the
other same-seed retained compact cores. A bounded actual rooted observation
then excludes those cores at large spatial scales. Other seed frames remain an
explicit exception until the original physical near-event identifies the frame.
No population complement of one selected core is charged here.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- A positive original label separation eventually dominates the bounded
rooted radius at its literal inverse spatial scale. -/
theorem exists_scale_threshold_for_rooted_radius (R : ℝ) {radius : ℝ}
    (hradius : 0 < radius) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      0 < scale ∧ R / scale < radius := by
  let threshold := (|R| + 1) / radius + 1
  have hthreshold : 0 < threshold := by dsimp only [threshold]; positivity
  refine ⟨threshold, hthreshold, ?_⟩
  intro scale hs
  have hscale : 0 < scale := hthreshold.trans_le hs
  refine ⟨hscale, (div_lt_iff₀ hscale).mpr ?_⟩
  have hlt : (|R| + 1) / radius < scale := by dsimp only [threshold] at hs; linarith
  have hmul := (div_lt_iff₀ hradius).mp hlt
  nlinarith [le_abs_self R]

/-- Every retained endpoint in the selected compact macroscopic label window
comes from the selected original core, or from a genuinely different seed frame.
The radius is uniform over the whole selected compact `K` and is chosen before
the spatial scale, actual root, endpoint, and retained competing core. -/
theorem exists_macro_radius_retained_core_index_or_cross_seed
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {I : Type*} [Fintype I]
    (C : I → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (C i).roots (C j).roots))
    (hlabel : ∀ j, ContinuousOn
      (populationSeedRootLabelValue (P (C j).seedIndex).seed a) (C j).roots)
    (i : I) {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ (C i).roots) :
    ∃ radius > 0, ∀ scale : ℝ, 0 < scale →
      ∀ root : Fin (finrank ℝ (P (C i).seedIndex).seed.covector.ker) → ℝ, ∀ R : ℝ,
      (∃ z ∈ K, dist (scale⁻¹ • root)
        ((Module.finBasis ℝ (P (C i).seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P (C i).seedIndex).seed a z)) < radius) →
      R / scale < radius → ∀ j : I, ∀ x : M, a x ∈ (C j).roots →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (C i).seedIndex scale x - root‖ ≤ R →
      j = i ∨ (C j).seedIndex ≠ (C i).seedIndex := by
  let bW := Module.finBasis ℝ (P (C i).seedIndex).seed.covector.ker
  let f := fun z ↦ bW.equivFun
    (populationSeedRootLabelValue (P (C i).seedIndex).seed a z)
  let J := {j : I // j ≠ i ∧ (C j).seedIndex = (C i).seedIndex}
  let bad := ⋃ j : J, f '' (C j.val).roots
  have hcont (j : I) (hseed : (C j).seedIndex = (C i).seedIndex) :
      ContinuousOn f (C j).roots := by
    have hc : ContinuousOn
        (populationSeedRootLabelValue (P (C i).seedIndex).seed a) (C j).roots := by
      exact Eq.mp (congrArg (fun seed : ℕ ↦ ContinuousOn
        (populationSeedRootLabelValue (P seed).seed a) (C j).roots) hseed) (hlabel j)
    exact bW.equivFunL.continuous.comp_continuousOn hc
  have hgood : IsCompact (f '' K) :=
    hK.image_of_continuousOn ((hcont i rfl).mono hsub)
  have hbad : IsCompact bad :=
    isCompact_iUnion (fun j : J ↦
      (C j.val).roots_compact.image_of_continuousOn (hcont j.val j.property.2))
  have hseparate : Disjoint (f '' K) bad := by
    apply Set.disjoint_left.mpr
    intro w hw hwb
    obtain ⟨z, hz, hzw⟩ := hw
    obtain ⟨j, z', hz', hz'w⟩ := Set.mem_iUnion.mp hwb
    have hzpiece : z ∈ populationSeedRootPiece P a κ lambda (C i).seedIndex :=
      (C i).roots_subset_piece (hsub hz)
    have hz'piece : z' ∈ populationSeedRootPiece P a κ lambda (C i).seedIndex := by
      simpa only [j.property.2] using (C j.val).roots_subset_piece hz'
    have hzz' : z = z' := fixed_seed_rootLabel_injOn hF hcomplete hu ha hinj
      (C i).seedIndex hzpiece hz'piece (bW.equivFun.injective (hzw.trans hz'w.symm))
    exact Set.disjoint_left.mp (hdisjoint j.property.1) hz' (hzz' ▸ hsub hz)
  obtain ⟨sep, hsep, hdist⟩ :=
    Metric.exists_pos_forall_lt_edist hgood hbad.isClosed hseparate
  let radius : ℝ := (sep : ℝ) / 3
  have hradius : 0 < radius := div_pos (by exact_mod_cast hsep) (by norm_num)
  refine ⟨radius, hradius, ?_⟩
  intro scale hscale root R hmacro hsmall j x hx hR
  by_cases hseed : (C j).seedIndex = (C i).seedIndex
  · left
    by_contra hji
    obtain ⟨z, hz, hmacro⟩ := hmacro
    have hximage : f (a x) ∈ bad :=
      Set.mem_iUnion.mpr ⟨⟨j, hji, hseed⟩, mem_image_of_mem f hx⟩
    have hsepdist : (sep : ℝ) < dist (f z) (f (a x)) := by
      simpa only [edist_dist, ENNReal.coe_lt_ofReal] using
        hdist (f z) (mem_image_of_mem f hz) (f (a x)) hximage
    have hlocal : dist (f (a x)) (scale⁻¹ • root) < radius :=
      (dist_physicalSceneOriginalSeedBasisPosition_macro_le
        (C i).seedIndex scale hscale root x R hR).trans_lt hsmall
    have hsum : dist (f z) (f (a x)) < radius + radius :=
      (dist_triangle (f z) (scale⁻¹ • root) (f (a x))).trans_lt
        (add_lt_add (by simpa only [dist_comm] using hmacro)
          (by simpa only [dist_comm] using hlocal))
    dsimp only [radius] at hsum
    linarith
  · exact Or.inr hseed

variable {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {loss : ℝ≥0∞}

/-- On an actual retained near edge, membership of its physical source in the
fixed original seed piece eliminates the cross-seed exception. At large scales,
the original edge's auxiliary core index is exactly the selected index. -/
theorem PopulationLocalPressureCore.exists_fixed_seed_macro_retained_near_core_isolation
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ (D.haar.continuous.coefficient i).roots) :
    let C := D.haar.continuous.coefficient
    ∃ radius > 0, ∀ R : ℝ, ∃ threshold > 0,
      ∀ scale : ℝ, threshold ≤ scale →
      ∀ root : Fin (finrank ℝ (P (C i).seedIndex).seed.covector.ker) → ℝ,
      (∃ z ∈ K, dist (scale⁻¹ • root)
        ((Module.finBasis ℝ (P (C i).seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P (C i).seedIndex).seed a z)) < radius) →
      ∀ k : Fin D.haar.continuous.count, ∀ nearRadius : ℝ, ∀ p : M × M,
        p ∈ D.nearDisplacementEvent k nearRadius →
        p.1 ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) (C i).seedIndex →
        ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
          (C i).seedIndex scale p.1 - root‖ ≤ R → k = i := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient
  have hlabel (j : Fin D.haar.continuous.count) : ContinuousOn
      (populationSeedRootLabelValue (P (C j).seedIndex).seed a) (C j).roots := by
    rw [← D.haar.intensity_roots j]
    exact (D.haar.intensity j).continuous_label
  obtain ⟨radius, hradius, hiso⟩ :=
    exists_macro_radius_retained_core_index_or_cross_seed hF hcomplete hu ha hinj
      C D.haar.continuous.disjoint hlabel i hK hsub
  refine ⟨radius, hradius, ?_⟩
  intro R
  obtain ⟨threshold, hthreshold, hlarge⟩ :=
    exists_scale_threshold_for_rooted_radius R hradius
  refine ⟨threshold, hthreshold, ?_⟩
  intro scale hs root hmacro k nearRadius p hp hsource hR
  have hseed : (C k).seedIndex = (C i).seedIndex := by
    by_contra hneq
    exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda hneq)
      ((C k).roots_subset_piece hp.1) hsource
  exact (hiso scale (hlarge scale hs).1 root R hmacro (hlarge scale hs).2
    k p.1 hp.1 hR).resolve_right (not_not.mpr hseed)

end OTSelector.Reconstruction
