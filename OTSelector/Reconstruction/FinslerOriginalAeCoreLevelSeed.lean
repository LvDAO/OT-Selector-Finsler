import OTSelector.Reconstruction.FinslerOriginalFrozenCoreEntryBound
import OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery

/-!
# A.e. core data and the frozen-core lane

Task-192/task-197 showed that the window chart producer of the reconstruction is
paper-faithful only in an almost-everywhere form: the paper's general argument
supplies a.e. ray-geometry data (Assouline ray clusters on Borel domains, full
measure subsets, no open foliation) rather than a pointwise smooth open chart.
This file addresses the frozen-core lane: its geometric input is shown to need
only a.e. data, so the a.e. core data suffices for that lane.

1. |AeSeedRayCoverage|: the paper's a.e. ray-cluster input in seed form --- for
   a.e. point of the law, the point lies on one of the seed's complete
   calibrated rays, with matching ray label and clock in the calibration span.
   No open set and no pointwise exact readout is required.
2. |AeSeedRayCoverage.endpointRecovery|: on the a.e. potential-regular domain,
   the a.e. ray-geometry interface (label locality along calibrated pairs and
   the physical inverse, both only asserted on the regular domain) turns a.e.
   ray coverage into the exact seed readout
   |x = S.curve (R (a x)) (u x - level)| almost everywhere.  This is the
   paper-faithful replacement of the pointwise readout in
   |FrozenCoreEdgeGeometry|.
3. |AeFrozenCoreEdgeGeometry| and |ae_frozenCoreEdgeGeometry|: the a.e.
   geometric hypotheses of a retained frozen-core edge transfer through the
   sample laws to |FrozenCoreEdgeGeometry| almost surely on the sample.  Only
   combinatorial mask data remains pointwise (supplied by the Taylor partition).
4. The a.e. amplitude-ball entry bound: the good-event per-edge bound of the
   frozen core, with kinetic-class constant |k * (4 * Drad) + 2 * (|t| * Bg)|,
   holds almost surely when its geometric and probe inputs hold almost surely.
5. |finiteDominationInequality_frozenCore_of_ae|: combining items 3 and 4 with
   the stochastic finite-domination interface, a.e. core data suffices for the
   frozen-core lane: the normalized masked frozen cost and the normalized
   perturbed value satisfy |FiniteDominationInequality|.

## Exact remaining sub-gap

The frozen-core lane is closed at the a.e. level.  The consumers that remain
pointwise-only are on the *window chart* side, not on the frozen-core side:

* |exists_levelSeedPatch_of_chartData| and the open-domain constructor
  |exists_chartData_of_ballCore| consume the pointwise smooth chart datum on an
  open set (the |CoreSectionChartData| fields); the a.e. chart datum of
  |FinslerOriginalWindowChartAe| does not feed them.
* The seed patch (|CalibratedLevelSeedPatch|) supplying the a.e. readout is
  constructed data with pointwise fields (complete calibrated curves, clock,
  calibration span); it is not a geometric hypothesis about a.e. points.
* The a.e. ray coverage |AeSeedRayCoverage| is the paper's Assouline ray-cluster
  package in seed form.  It is not derived here from a formalized Assouline
  theorem (the repository contains none); in the population reconstruction the
  same a.e. readout is produced by
  |PopulationHaarPressureCore.physical_endpoints_ae| from the constructed
  conditional laws, so the coverage input is available in the actual lane.
-/
open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [BorelSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  [MeasurableSpace.CountablySeparated Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

section CoreGeometry

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instAeCoreLaneMetric : MetricSpace M := F.metricSpace
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-! ## A.e. ray coverage and a.e. seed readout -/

end CoreGeometry

/-- **A.e. ray coverage of the seed's calibrated rays.**  The paper's a.e.
ray-cluster input in seed form: for almost every point of the law whose label is
a retained root, the point lies on one of the seed's complete calibrated rays,
the ray label equals the point's label, and the point's clock time lies in the
calibration span of that ray. -/
def AeSeedRayCoverage (S : F.CalibratedLevelSeedPatch u) (a : M → Z) (roots : Set Z)
    (η : Measure M) : Prop :=
  ∀ᵐ x ∂η, a x ∈ roots →
    ∃ w : S.covector.ker, w ∈ S.labels ∧ a x = a (S.curve w 0) ∧
      u x - (S.level : ℝ) ∈ interior (S.calibrationTimes w)

section CoreGeometry

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instAeCoreLaneMetric : MetricSpace M := F.metricSpace
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **A.e. exact seed readout from a.e. ray coverage.**  On the a.e.
potential-regular domain, label locality along calibrated pairs and the physical
inverse identity (both only asserted on the regular domain) turn the a.e. ray
coverage into the exact seed readout almost everywhere. -/
theorem AeSeedRayCoverage.endpointRecovery
    (S : F.CalibratedLevelSeedPatch u)
    (horder : let _instAeSeedRecoveryOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {b : Z × ℝ → M}
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    {roots : Set Z} {η : Measure M}
    (hreg : ∀ᵐ x ∂η, x ∈ F.potentialRegularDomain u)
    (cov : AeSeedRayCoverage S a roots η) :
    ∀ᵐ x ∂η, a x ∈ roots →
      x = S.curve (populationSeedRootLabelValue S a (a x)) (u x - (S.level : ℝ)) := by
  filter_upwards [hreg, cov] with x hxreg hx
  intro hxroot
  obtain ⟨w, hw, hlabel, htime⟩ := hx hxroot
  have hR : populationSeedRootLabelValue S a (a x) = w := by
    rw [hlabel]
    exact populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj ⟨w, hw⟩
  have hseed :=
    seed_curve_eq_original_inverse_on_active S hF hcomplete hu horder hinv hw htime
  rw [show (S.level : ℝ) + (u x - (S.level : ℝ)) = u x by ring, hlabel.symm] at hseed
  rw [hR]
  exact (hinv x hxreg).symm.trans hseed

/-! ## A.e. frozen-core edge geometry -/

/-- **The a.e. geometric hypotheses of a retained frozen-core edge.**  All
geometric content is stated almost everywhere on the source law, the target law
and their pair law: root membership and the exact seed readout on the marginals,
and the window-region containment on the pair law.  No open domain, no pointwise
readout and no a.e. chart are required. -/
structure AeFrozenCoreEdgeGeometry
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {ε : ℝ}
    (D : C.TaylorRootCover ε) where
  /-- The Taylor root cover has a nonempty center set (combinatorial data). -/
  centers_nonempty : D.centers.Nonempty
  /-- Root membership for a.e. source. -/
  source_root : ∀ᵐ x ∂η₀, a x ∈ C.roots
  /-- Root membership for a.e. target. -/
  target_root : ∀ᵐ y ∂η₁, a y ∈ C.roots
  /-- The clock pair lies in the scalar window region for a.e. pair. -/
  pair_window : ∀ᵐ p ∂(η₀.prod η₁), (u p.1, u p.2) ∈ C.window.region
  /-- The exact seed readout for a.e. source. -/
  source_readout : ∀ᵐ x ∂η₀, a x ∈ C.roots →
    x = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x))
      (u x - ((P C.seedIndex).seed.level : ℝ))
  /-- The exact seed readout for a.e. target. -/
  target_readout : ∀ᵐ y ∂η₁, a y ∈ C.roots →
    y = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y))
      (u y - ((P C.seedIndex).seed.level : ℝ))

/-- **A.e. core data builds the a.e. frozen-core geometry.**  A.e. ray coverage
together with a.e. root membership, a.e. potential regularity, the a.e. pair
window condition and the a.e. ray-geometry interface produce the a.e. geometric
hypotheses of the frozen core. -/
theorem AeFrozenCoreEdgeGeometry.ofAeSeedRayCoverage
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {D : C.TaylorRootCover ε}
    (horder : let _instAeCoreGeometryOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {b : Z × ℝ → M}
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hreg₀ : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hreg₁ : ∀ᵐ y ∂η₁, y ∈ F.potentialRegularDomain u)
    (cov₀ : AeSeedRayCoverage (P C.seedIndex).seed a C.roots η₀)
    (cov₁ : AeSeedRayCoverage (P C.seedIndex).seed a C.roots η₁)
    (hroot₀ : ∀ᵐ x ∂η₀, a x ∈ C.roots)
    (hroot₁ : ∀ᵐ y ∂η₁, a y ∈ C.roots)
    (hwindow : ∀ᵐ p ∂(η₀.prod η₁), (u p.1, u p.2) ∈ C.window.region)
    (hcenters : D.centers.Nonempty) :
    AeFrozenCoreEdgeGeometry C D where
  centers_nonempty := hcenters
  source_root := hroot₀
  target_root := hroot₁
  pair_window := hwindow
  source_readout :=
    AeSeedRayCoverage.endpointRecovery hF hcomplete hu ha hinj (P C.seedIndex).seed
      horder hinv hreg₀ cov₀
  target_readout :=
    AeSeedRayCoverage.endpointRecovery hF hcomplete hu ha hinj (P C.seedIndex).seed
      horder hinv hreg₁ cov₁

/-- **A.e. geometry transfers to a.e. |FrozenCoreEdgeGeometry|.**  Finite index
sets and the sample laws turn the a.e. marginal and pair-law hypotheses into
|FrozenCoreEdgeGeometry| on every retained edge almost surely.  Only the
combinatorial mask data (Taylor partition cells and centers) is needed
pointwise. -/
theorem ae_frozenCoreEdgeGeometry
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {D : C.TaylorRootCover ε} (G : AeFrozenCoreEdgeGeometry C D)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} {n : ℕ}
    (X Y : Ω → Fin n → M) (Q : Ω → Set (Fin n × Fin n))
    (z₀ : Ω → Fin n → Fin n → Z)
    (hX : ∀ i, Measurable fun ξ => X ξ i)
    (hY : ∀ j, Measurable fun ξ => Y ξ j)
    (hXlaw : ∀ i, sample.map (fun ξ => X ξ i) = η₀)
    (hYlaw : ∀ j, sample.map (fun ξ => Y ξ j) = η₁)
    (hpair : ∀ i j, sample.map (fun ξ => (X ξ i, Y ξ j)) = η₀.prod η₁)
    (hcenter : ∀ᵐ ξ ∂sample, ∀ i j, z₀ ξ i j ∈ D.centers)
    (hmask : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      a (X ξ i) ∈ C.roots ∩ D.neighborhood (z₀ ξ i j) ∧
      a (Y ξ j) ∈ C.roots ∩ D.neighborhood (z₀ ξ i j) ∧
      (u (X ξ i), u (Y ξ j)) ∈ C.window.region) :
    ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      FrozenCoreEdgeGeometry C D (z₀ ξ) (X ξ) (Y ξ) i j := by
  have hreadX : ∀ᵐ ξ ∂sample, ∀ i, a (X ξ i) ∈ C.roots →
      X ξ i = (P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (X ξ i)))
        (u (X ξ i) - ((P C.seedIndex).seed.level : ℝ)) := by
    rw [ae_all_iff]
    intro i
    exact ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact G.source_readout)
  have hreadY : ∀ᵐ ξ ∂sample, ∀ j, a (Y ξ j) ∈ C.roots →
      Y ξ j = (P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (Y ξ j)))
        (u (Y ξ j) - ((P C.seedIndex).seed.level : ℝ)) := by
    rw [ae_all_iff]
    intro j
    exact ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact G.target_readout)
  filter_upwards [hreadX, hreadY, hcenter, hmask] with ξ hrX hrY hc hk
  intro i j hij
  obtain ⟨hxi, hyj, hp⟩ := hk i j hij
  exact ⟨hc i j, hxi, hyj, hp, hrX i hxi.1, hrY j hyj.1⟩

end CoreGeometry

/-! ## The a.e. amplitude-ball entry bound -/

section AeEntryBound

variable [PseudoMetricSpace M]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instAeEntryMetric : MetricSpace M := F.metricSpace
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **A.e. good-event per-edge bound.**  The frozen-core entry bound of the
kinetic-class amplitude lane holds almost surely as soon as its geometric and
probe inputs hold almost surely: no pointwise geometric hypothesis is needed. -/
theorem frozenCoreMatrix_le_of_ball_ae
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (Dm : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ} (hφu : ∀ x, φ x = u x) (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} {n : ℕ}
    (X Y : Ω → Fin n → M) (Q : Ω → Set (Fin n × Fin n))
    (z₀ : Ω → Fin n → Fin n → Z)
    (h : Ω → Matrix (Fin n) (Fin n) ℝ) (g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hgeom : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      FrozenCoreEdgeGeometry C Dm (z₀ ξ) (X ξ) (Y ξ) i j)
    (hgh : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      |g ξ i j - h ξ i j| ≤ probeError)
    (hg_bound : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg)
    {c : M} {Drad : ℝ}
    (hX : ∀ᵐ ξ ∂sample, ∀ i, dist (X ξ i) c ≤ Drad)
    (hY : ∀ᵐ ξ ∂sample, ∀ j, dist (Y ξ j) c ≤ Drad) :
    ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      frozenCoreMatrix C ε (z₀ ξ) (X ξ) (Y ξ) k t (h ξ) i j ≤
        k * (4 * Drad) + 2 * (|t| * Bg) := by
  filter_upwards [hgeom, hgh, hg_bound, hX, hY] with ξ hg hghξ hgb hXξ hYξ
  intro i j hij
  exact frozenCoreMatrix_le_of_ball hF hcomplete hu ha hinj
    Dm hε hε1 hdist hφu hφ hk hg hghξ hgb hprobeError_le hXξ hYξ i j hij

/-- **A.e. masked per-edge bound.**  The masked frozen-core matrix on the
retained mask is bounded by the kinetic-class constant almost surely. -/
theorem maskedFrozenCoreMatrix_entryBound_of_ball_ae
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (Dm : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ} (hφu : ∀ x, φ x = u x) (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} {n : ℕ}
    (X Y : Ω → Fin n → M) (Q : Ω → Set (Fin n × Fin n))
    (z₀ : Ω → Fin n → Fin n → Z)
    (h : Ω → Matrix (Fin n) (Fin n) ℝ) (g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hgeom : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      FrozenCoreEdgeGeometry C Dm (z₀ ξ) (X ξ) (Y ξ) i j)
    (hgh : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      |g ξ i j - h ξ i j| ≤ probeError)
    (hg_bound : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg)
    {c : M} {Drad : ℝ} (hDrad : 0 ≤ Drad) (hBg : 0 ≤ Bg)
    (hX : ∀ᵐ ξ ∂sample, ∀ i, dist (X ξ i) c ≤ Drad)
    (hY : ∀ᵐ ξ ∂sample, ∀ j, dist (Y ξ j) c ≤ Drad) :
    ∀ᵐ ξ ∂sample, ∀ i j,
      maskedFrozenCost (Q ξ) (frozenCoreMatrix C ε (z₀ ξ) (X ξ) (Y ξ) k t (h ξ)) i j ≤
        k * (4 * Drad) + 2 * (|t| * Bg) := by
  filter_upwards [hgeom, hgh, hg_bound, hX, hY] with ξ hg hghξ hgb hXξ hYξ
  intro i j
  exact maskedFrozenCoreMatrix_entryBound_of_ball hF hcomplete hu ha hinj
    Dm hε hε1 hdist hφu hφ hk hg hghξ hgb hprobeError_le hDrad hBg hXξ hYξ i j

/-- **A.e. normalized frozen-core cost bound.**  On the good event the
normalized masked frozen-core cost of any doubly stochastic fractional assignment
is bounded by the kinetic-class constant almost surely. -/
theorem maskedFrozenCoreCost_div_le_of_ball_ae
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (Dm : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ} (hφu : ∀ x, φ x = u x) (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k) {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω}
    (X Y : Ω → Fin n → M) (Q : Ω → Set (Fin n × Fin n))
    (z₀ : Ω → Fin n → Fin n → Z)
    (h : Ω → Matrix (Fin n) (Fin n) ℝ) (g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (Pmat : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hgeom : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      FrozenCoreEdgeGeometry C Dm (z₀ ξ) (X ξ) (Y ξ) i j)
    (hgh : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      |g ξ i j - h ξ i j| ≤ probeError)
    (hg_bound : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg)
    {c : M} {Drad : ℝ} (hDrad : 0 ≤ Drad) (hBg : 0 ≤ Bg)
    (hX : ∀ᵐ ξ ∂sample, ∀ i, dist (X ξ i) c ≤ Drad)
    (hY : ∀ᵐ ξ ∂sample, ∀ j, dist (Y ξ j) c ≤ Drad)
    (hP : ∀ᵐ ξ ∂sample, Pmat ξ ∈ doublyStochastic ℝ (Fin n)) :
    ∀ᵐ ξ ∂sample,
      fractionalAssignmentCost
          (maskedFrozenCost (Q ξ)
            (frozenCoreMatrix C ε (z₀ ξ) (X ξ) (Y ξ) k t (h ξ))) (Pmat ξ) /
          (n : ℝ) ≤
        k * (4 * Drad) + 2 * (|t| * Bg) := by
  filter_upwards [hgeom, hgh, hg_bound, hX, hY, hP] with ξ hg hghξ hgb hXξ hYξ hPξ
  exact maskedFrozenCoreCost_div_le_of_ball hF hcomplete hu ha hinj
    Dm hε hε1 hdist hφu hφ hk hg hghξ hgb hprobeError_le hDrad hBg hXξ hYξ hPξ hn

end AeEntryBound

/-! ## A.e. core data suffices for the frozen-core lane -/

/-- **The frozen-core finite-domination inequality from a.e. core data.**

The a.e. geometric hypotheses |AeFrozenCoreEdgeGeometry|, transported through
the sample laws, together with almost-sure optimality and probe hypotheses give
the finite-domination inequality for the normalized masked frozen core.  No
pointwise geometric edge hypothesis is consumed. -/
theorem finiteDominationInequality_frozenCore_of_ae
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAeFiniteDominationMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ} (hφu : ∀ x, φ x = u x) (hφ : LipschitzWith 1 φ)
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω}
    (X Y : ∀ n, Ω → Fin (N n) → M)
    (z₀ : ∀ n, Ω → Fin (N n) → Fin (N n) → Z)
    (h : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (g : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {Q : ∀ n, Ω → Set (Fin (N n) × Fin (N n))}
    (Pmat : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hX : ∀ n i, Measurable fun ξ => X n ξ i)
    (hY : ∀ n j, Measurable fun ξ => Y n ξ j)
    (hXlaw : ∀ n i, sample.map (fun ξ => X n ξ i) = η₀)
    (hYlaw : ∀ n j, sample.map (fun ξ => Y n ξ j) = η₁)
    (hpair : ∀ n i j, sample.map (fun ξ => (X n ξ i, Y n ξ j)) = η₀.prod η₁)
    (hcenter : ∀ n, ∀ᵐ ξ ∂sample, ∀ i j, z₀ n ξ i j ∈ D.centers)
    (hmask : ∀ n, ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q n ξ →
      a (X n ξ i) ∈ C.roots ∩ D.neighborhood (z₀ n ξ i j) ∧
      a (Y n ξ j) ∈ C.roots ∩ D.neighborhood (z₀ n ξ i j) ∧
      (u (X n ξ i), u (Y n ξ j)) ∈ C.window.region)
    (hbase : AeFrozenCoreEdgeGeometry C D)
    (hP : ∀ n, ∀ᵐ ξ ∂sample, OptimalFractionalAssignment
      (perturbedEdgeCost
        (fun i j => k * distanceSlackEdgeCost (X n ξ) (Y n ξ) φ i j) (g n ξ) t)
      (Pmat n ξ))
    (hgh : ∀ n, ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q n ξ →
      |g n ξ i j - h n ξ i j| ≤ probeError)
    (hg_bound : ∀ n, ∀ᵐ ξ ∂sample, ∀ i j, |g n ξ i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg) :
    OTSelector.PointProcess.FiniteDominationInequality sample
      (fun n ξ => fractionalAssignmentCost
        (maskedFrozenCost (Q n ξ)
          (frozenCoreMatrix C ε (z₀ n ξ) (X n ξ) (Y n ξ) k t (h n ξ)))
        (Pmat n ξ) / (N n : ℝ))
      (fun n ξ => perturbedAssignmentValue
        (fun i j => k * distanceSlackEdgeCost (X n ξ) (Y n ξ) φ i j)
        (g n ξ) t / (N n : ℝ))
      (|t| * Bg) := by
  have hgeom : ∀ n, ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q n ξ →
      FrozenCoreEdgeGeometry C D (z₀ n ξ) (X n ξ) (Y n ξ) i j := fun n =>
    ae_frozenCoreEdgeGeometry hF hcomplete hu ha hinj hbase
      (X n) (Y n) (Q n) (z₀ n) (hX n) (hY n) (hXlaw n) (hYlaw n)
      (hpair n) (hcenter n) (hmask n)
  exact finiteDominationInequality_of_geometric_probeBound hF hcomplete hu ha hinj
    D hε hε1 hdist hφu hφ hN X Y z₀ h g hk Pmat hP hgeom hgh hg_bound
    hprobeError_le

end OTSelector.Reconstruction
