import OTSelector.Reconstruction.FinslerCoefficientCoreTaylorCover
import OTSelector.Reconstruction.FinslerSplicedDistancePressure
import OTSelector.Reconstruction.FiniteTileSplicedPressure

/-!
# Finite geometric tiles in the original global distance pressure

Every retained tile uses its own actual seed basis and coefficient. The physical
sample arrays are unchanged, and only edges joining roots in one common Taylor
neighborhood are replaced by their frozen quadratic costs.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- A tile's frozen cost evaluated on the original physical sample points, using
its own retained seed basis and its actual population scalar coordinates. -/
def OriginalPopulationCoefficientCore.frozenPhysicalCost
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (z₀ : Z) (x y : M) : ℝ :=
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a
  let v := (Module.finBasis ℝ S.covector.ker).equivFun (w (a y) - w (a x))
  matrixQuadratic (C.matrix z₀ (u x, u y)) v

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instTileMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The physical frozen coefficient is measurable jointly in the reference root
and the original source and target sample points. -/
theorem OriginalPopulationCoefficientCore.measurable_frozenPhysicalCost
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {Ω : Type*} [MeasurableSpace Ω] {z : Ω → Z} {X Y : Ω → M}
    (hz : Measurable z) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ξ ↦ C.frozenPhysicalCost (z ξ) (X ξ) (Y ξ)) := by
  let _instTileMetric : MetricSpace M := F.metricSpace
  let S := (P C.seedIndex).seed
  let bW := Module.finBasis ℝ S.covector.ker
  have hw := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  exact C.measurable_quadratic_cost hF hcomplete hu ha hinj hz
    ((hu.continuous.measurable.comp hX).prodMk (hu.continuous.measurable.comp hY))
    (bW.equivFunL.continuous.measurable.comp
      ((hw.comp (ha.comp hY)).sub (hw.comp (ha.comp hX))))

/-- The produced Taylor cover controls the actual physical distance edge. Only
its exact coordinate readout and tile membership enter this pointwise statement. -/
theorem OriginalPopulationCoefficientCore.TaylorRootCover.physical_relative
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) {z₀ : Z} {x y : M}
    (hz₀ : z₀ ∈ D.centers)
    (hx : a x ∈ C.roots ∩ D.neighborhood z₀)
    (hy : a y ∈ C.roots ∩ D.neighborhood z₀)
    (hp : (u x, u y) ∈ C.window.region)
    (hxread : x = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x))
      (u x - (P C.seedIndex).seed.level))
    (hyread : y = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y))
      (u y - (P C.seedIndex).seed.level)) :
    |((F.lengthEDist x y).toReal - u y + u x) - C.frozenPhysicalCost z₀ x y| ≤
      (2 * ε) * C.frozenPhysicalCost z₀ x y := by
  have hb := D.relative_distance hF hcomplete hu ha hinj hε hz₀ hx hy hp
  change |populationSeedPairDeficit (P C.seedIndex).seed (u x, u y)
    (populationSeedRootLabelValue (P C.seedIndex).seed a (a x),
      populationSeedRootLabelValue (P C.seedIndex).seed a (a y)) -
    C.frozenPhysicalCost z₀ x y| ≤ (2 * ε) * C.frozenPhysicalCost z₀ x y at hb
  simpa only [populationSeedPairDeficit, ← hxread, ← hyread] using hb

/-- All retained geometric tiles can be frozen simultaneously in the original
sample pressure. The theorem derives edge integrability from compact carriers;
no sample balance or optimizer moment is required for any tile. -/
theorem expected_finite_finsler_pressure
    {Tile : Type*} [Fintype Tile] (C : Tile → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {ε : ℝ} (D : ∀ k, (C k).TaylorRootCover ε)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} (hn : 0 < n)
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hXA : ∀ i, ∀ᵐ ξ ∂sample, X ξ i ∈ A)
    (hYB : ∀ j, ∀ᵐ ξ ∂sample, Y ξ j ∈ B)
    (Q : Ω → Tile → Set (Fin n × Fin n))
    (hQ : ∀ k i j, MeasurableSet {ξ | (i, j) ∈ Q ξ k})
    (hdisjoint : ∀ᵐ ξ ∂sample, Pairwise (fun k l ↦ Disjoint (Q ξ k) (Q ξ l)))
    (z₀ : Ω → Tile → Fin n → Fin n → Z)
    (hz₀ : ∀ k i j, Measurable (fun ξ ↦ z₀ ξ k i j))
    (hgeometry : ∀ᵐ ξ ∂sample, ∀ k i j, (i, j) ∈ Q ξ k →
      z₀ ξ k i j ∈ (D k).centers ∧
      a (X ξ i) ∈ (C k).roots ∩ (D k).neighborhood (z₀ ξ k i j) ∧
      a (Y ξ j) ∈ (C k).roots ∩ (D k).neighborhood (z₀ ξ k i j) ∧
      (u (X ξ i), u (Y ξ j)) ∈ (C k).window.region ∧
      X ξ i = (P (C k).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (C k).seedIndex).seed a (a (X ξ i)))
        (u (X ξ i) - (P (C k).seedIndex).seed.level) ∧
      Y ξ j = (P (C k).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (C k).seedIndex).seed a (a (Y ξ j)))
        (u (Y ξ j) - (P (C k).seedIndex).seed.level))
    (g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (h : Ω → Tile → Matrix (Fin n) (Fin n) ℝ)
    (t G probeError scale : ℝ) (hε0 : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hscale : 0 ≤ scale) (hprobe : 0 ≤ probeError)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hh : ∀ k i j, Measurable (fun ξ ↦ h ξ k i j))
    (hgb : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ G)
    (hhb : ∀ᵐ ξ ∂sample, ∀ k i j, (i, j) ∈ Q ξ k → |h ξ k i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂sample, ∀ k i j, (i, j) ∈ Q ξ k →
      |g ξ i j - h ξ k i j| ≤ probeError) :
    let c := fun ξ i j ↦ scale *
      ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))
    let d := fun ξ k i j ↦ scale * (C k).frozenPhysicalCost (z₀ ξ k i j) (X ξ i) (Y ξ j)
    let dQ := fun ξ ↦ finiteTileSplice (Q ξ) (c ξ) (d ξ)
    let hQ := fun ξ ↦ finiteTileSplice (Q ξ) (g ξ) (h ξ)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / n) sample ∧
      Integrable (fun ξ ↦ perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n) sample ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂sample) -
        ∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂sample| ≤
      (2 * ε) * ((∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂sample) +
        |t| * G) + |t| * probeError := by
  let _instTileMetric : MetricSpace M := F.metricSpace
  let _instTileProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨hcm, hci, hcn⟩ := scaled_distanceSlack_sampling_data X Y u hu hX hY
    hA hB hXA hYB hscale
  have hdm (k : Tile) (i j : Fin n) : Measurable (fun ξ ↦
      scale * (C k).frozenPhysicalCost (z₀ ξ k i j) (X ξ i) (Y ξ j)) :=
    ((C k).measurable_frozenPhysicalCost hF hcomplete hu ha hinj
      (hz₀ k i j) (hX i) (hY j)).const_mul scale
  apply expected_finiteTileSplice_pressure hn Q
    (fun ξ i j ↦ scale * distanceSlackEdgeCost (X ξ) (Y ξ) u i j) g
    (fun ξ k i j ↦ scale * (C k).frozenPhysicalCost (z₀ ξ k i j) (X ξ i) (Y ξ j)) h
    t (2 * ε) G probeError (mul_nonneg (by norm_num) hε0) hε1 hprobe
    hQ hdisjoint hcm hg hdm hh hci (Filter.Eventually.of_forall hcn) _ hgb hhb hgh
  filter_upwards [hgeometry] with ξ hgeometryξ
  intro k i j hij
  obtain ⟨hc, hx, hy, hp, hxr, hyr⟩ := hgeometryξ k i j hij
  have hb := (D k).physical_relative hF hcomplete hu ha hinj hε0 hc hx hy hp hxr hyr
  change |scale * ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i)) -
    scale * (C k).frozenPhysicalCost (z₀ ξ k i j) (X ξ i) (Y ξ j)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left hb hscale).trans_eq (by ring)

end OTSelector.Reconstruction
