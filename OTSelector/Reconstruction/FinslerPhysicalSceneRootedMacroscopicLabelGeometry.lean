import OTSelector.Geometry.Finsler.Calibration.SeedCoordinateRecovery
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed
import OTSelector.Reconstruction.FinslerCoefficientCoreTaylorCover

/-!
# Geometry.Finsler.Calibration.SeedCoordinateRecovery

* **Conditions:** The same fixed seed observation and a point/root in the actual original selected seed piece.
* **Objects:** Exact recovery of the inverse seed vector and its original population label from the unchanged basis coordinates.
* **Proof detail:** Cancel the basis equivalence and its inverse, then apply the actual inverse seed-label identity on its image.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (adapter): Only the three exact root-readout identities are selected; macroscopic/residual decompositions and continuity refinements are outside scope.
-/

/-!
# Original seed labels at the actual macroscopic root

The fixed original seed basis recovers the original population label exactly.
The actual scaled observation separates into its macroscopic root and local
residual. On a compact continuous-label core, original root recovery supplies
inverse continuity, hence a genuine root-neighborhood test from these labels.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Rescaling
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The original coordinate is exactly the macroscopic root plus its actual
rescaled rooted residual. -/
theorem coordinate_eq_macro_add_scaled_rooted_residual
    (scale : ℝ) (hscale : scale ≠ 0) (b z : V) :
    b = scale⁻¹ • z + scale⁻¹ • (scale • b - z) := by
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hscale, one_smul]
  abel

/-- A bounded actual rooted window gives the physical coordinate distance to
the actual macroscopic root, with exactly its inverse spatial scale. -/
theorem dist_coordinate_macro_le_of_rooted_residual
    (scale : ℝ) (hscale : 0 < scale) (b z : V) (R : ℝ)
    (hR : ‖scale • b - z‖ ≤ R) : dist b (scale⁻¹ • z) ≤ R / scale := by
  have heq : b - scale⁻¹ • z = scale⁻¹ • (scale • b - z) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  exact (mul_le_mul_of_nonneg_left hR (le_of_lt (inv_pos.mpr hscale))).trans_eq (by ring)

end Rescaling

section CompactInverse
variable {Z V : Type*} [TopologicalSpace Z] [MetricSpace V]

/-- A continuous injective label on a compact original root core has a
quantitative inverse-neighborhood radius, requiring no ambient continuity of
the original root map. -/
theorem exists_label_radius_into_open_of_compact_injOn
    {K U : Set Z} (hK : IsCompact K) (hU : IsOpen U)
    (f : Z → V) (hf : ContinuousOn f K) (hinj : InjOn f K)
    {z₀ : Z} (hz₀K : z₀ ∈ K) (hz₀U : z₀ ∈ U) :
    ∃ radius > 0, ∀ z ∈ K, dist (f z) (f z₀) < radius → z ∈ U := by
  have hbad : IsCompact (f '' (K \ U)) :=
    (hK.diff hU).image_of_continuousOn (hf.mono sdiff_subset)
  have hnot : f z₀ ∉ f '' (K \ U) := by
    rintro ⟨z, hz, heq⟩
    have hzz : z = z₀ := hinj hz.1 hz₀K heq
    exact hz.2 (hzz ▸ hz₀U)
  obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp hbad.isClosed.isOpen_compl
    (f z₀) hnot
  refine ⟨radius, hradius, ?_⟩
  intro z hz hdist
  by_contra hzU
  exact (hball (Metric.mem_ball.mpr hdist)) ⟨z, ⟨hz, hzU⟩, rfl⟩

/-- A macroscopic label near a retained center and a small local label
residual force the original root into that center's actual open neighborhood. -/
theorem exists_macro_label_radius_into_open_of_compact_injOn
    {K U : Set Z} (hK : IsCompact K) (hU : IsOpen U)
    (f : Z → V) (hf : ContinuousOn f K) (hinj : InjOn f K)
    {z₀ : Z} (hz₀K : z₀ ∈ K) (hz₀U : z₀ ∈ U) :
    ∃ radius > 0, ∀ z ∈ K, ∀ w : V,
      dist w (f z₀) < radius → dist (f z) w < radius → z ∈ U := by
  obtain ⟨radius, hradius, hmem⟩ :=
    exists_label_radius_into_open_of_compact_injOn hK hU f hf hinj hz₀K hz₀U
  refine ⟨radius / 2, half_pos hradius, ?_⟩
  intro z hz w hw hzw
  apply hmem z hz
  have htri := dist_triangle (f z) w (f z₀)
  linarith

end CompactInverse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}



variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))





include hF hcomplete hu ha hinj in
/-- Exact original root recovery makes the retained original label injective
on its fixed original root piece. -/
theorem fixed_seed_rootLabel_injOn (j : ℕ) :
    InjOn (populationSeedRootLabelValue (P j).seed a)
      (populationSeedRootPiece P a κ lambda j) := by
  intro z hz z' hz' heq
  have hr := (fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj j hz).2
  have hr' := (fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj j hz').2
  rw [← hr, ← hr', heq]

/-- The fixed original seed coordinate is the actual macroscopic root plus
its actual local rooted position at inverse spatial scale. -/
theorem physicalSceneOriginalSeedBasisPosition_eq_macro_add_rooted
    (j : ℕ) (scale : ℝ) (hscale : scale ≠ 0) (z :
      Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) (x : M) :
    physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x =
      scale⁻¹ • z + scale⁻¹ •
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale x - z) :=
  coordinate_eq_macro_add_scaled_rooted_residual scale hscale _ z

/-- Compact actual rooted spatial windows give the exact inverse-scale
closeness to the same original macroscopic root. -/
theorem dist_physicalSceneOriginalSeedBasisPosition_macro_le
    (j : ℕ) (scale : ℝ) (hscale : 0 < scale) (z :
      Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) (x : M) (R : ℝ)
    (hR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale x - z‖ ≤ R) :
    dist (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x) (scale⁻¹ • z) ≤
      R / scale :=
  dist_coordinate_macro_le_of_rooted_residual scale hscale _ z R hR

include hF hcomplete hu ha hinj in
/-- A genuine compact continuous-label core supplies a macroscopic label
neighborhood forcing actual original endpoints into the SAME original root
neighborhood used by TaylorRootCover.relative_distance. -/
theorem exists_fixed_seed_macro_radius_into_root_neighborhood
    (j : ℕ) {K U : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P j).seed a) K)
    (hU : IsOpen U) {z₀ : ℚ → M} (hz₀K : z₀ ∈ K) (hz₀U : z₀ ∈ U) :
    ∃ radius > 0, ∀ x : M, a x ∈ K → ∀ w :
      Fin (finrank ℝ (P j).seed.covector.ker) → ℝ,
      dist w ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P j).seed a z₀)) < radius →
      dist (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x) w < radius →
      a x ∈ K ∩ U := by
  let bW := Module.finBasis ℝ (P j).seed.covector.ker
  let f := fun z ↦ bW.equivFun (populationSeedRootLabelValue (P j).seed a z)
  have hf : ContinuousOn f K := bW.equivFunL.continuous.comp_continuousOn hlabel
  have hi : InjOn f K := by
    intro z hz z' hz' heq
    exact fixed_seed_rootLabel_injOn hF hcomplete hu ha hinj j (hsub hz) (hsub hz')
      (bW.equivFun.injective heq)
  obtain ⟨radius, hradius, hmem⟩ :=
    exists_macro_label_radius_into_open_of_compact_injOn hK hU f hf hi hz₀K hz₀U
  refine ⟨radius, hradius, ?_⟩
  intro x hx w hw hlocal
  exact ⟨hx, hmem (a x) hx w hw hlocal⟩

include hF hcomplete hu ha hinj in
/-- One actual macroscopic label window and a bounded local observation put
both retained original endpoint roots into the same original open root cell.
The radius is chosen before the spatial scale, root and physical endpoints. -/
theorem exists_fixed_seed_macro_rooted_window_into_root_neighborhood
    (j : ℕ) {K U : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P j).seed a) K)
    (hU : IsOpen U) {z₀ : ℚ → M} (hz₀K : z₀ ∈ K) (hz₀U : z₀ ∈ U) :
    ∃ radius > 0, ∀ scale : ℝ, 0 < scale →
      ∀ root : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ, ∀ R : ℝ,
      dist (scale⁻¹ • root) ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P j).seed a z₀)) < radius →
      R / scale < radius →
      ∀ x y : M, a x ∈ K → a y ∈ K →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale x - root‖ ≤ R →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale y - root‖ ≤ R →
      a x ∈ K ∩ U ∧ a y ∈ K ∩ U := by
  obtain ⟨radius, hradius, hmem⟩ := exists_fixed_seed_macro_radius_into_root_neighborhood
    hF hcomplete hu ha hinj j hK hsub hlabel hU hz₀K hz₀U
  refine ⟨radius, hradius, ?_⟩
  intro scale hscale root R hmacro hsmall x y hx hy hxR hyR
  exact ⟨hmem x hx (scale⁻¹ • root) hmacro
      ((dist_physicalSceneOriginalSeedBasisPosition_macro_le j scale hscale root x R hxR).trans_lt
        hsmall),
    hmem y hy (scale⁻¹ • root) hmacro
      ((dist_physicalSceneOriginalSeedBasisPosition_macro_le j scale hscale root y R hyR).trans_lt
        hsmall)⟩

end OTSelector.Reconstruction
