import OTSelector.Reconstruction.FinslerFrozenCoreDomination
import OTSelector.Reconstruction.FinslerPopulationSplicedPressure

/-!
# Simultaneous frozen-core domination on the original population samples

The original population reconstruction supplies the geometric hypotheses on
every retained Taylor edge almost surely. Disjointness then combines all tiles
before applying finite domination. The probe overhead is paid once for the
whole fractional assignment, independently of the number of tiles.
-/

open Set Function Matrix MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}

namespace PopulationLocalPressureCore.TaylorTiles

variable {ε : ℝ} (T : D.TaylorTiles ε)

/-- All actual retained edges have their own original seed readouts on one
full-measure sample event. Independence and a prescribed tile balance are unnecessary. -/
theorem ae_original_edge_geometry
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOriginalGeometryMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instOriginalGeometryOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} {n : ℕ}
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    (hXlaw : ∀ i, sample.map (fun ξ ↦ X ξ i) = η₀)
    (hYlaw : ∀ j, sample.map (fun ξ ↦ Y ξ j) = η₁) :
    ∀ᵐ ξ ∂sample, ∀ c : T.Index, ∀ i j, (i, j) ∈ T.edgeEvent (X ξ) (Y ξ) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (X ξ) (Y ξ) i j := by
  obtain ⟨hsource, htarget⟩ := D.haar.physical_endpoints_ae
    hF hcomplete hu ha hinj horder hb hinv hη₀reg hη₁reg
  have hXs : ∀ᵐ ξ ∂sample, ∀ i : Fin n, ∀ c : Fin D.haar.continuous.count,
      a (X ξ i) ∈ (D.haar.continuous.coefficient c).roots →
      let S := (P (D.haar.continuous.coefficient c).seedIndex).seed
      X ξ i = S.curve (populationSeedRootLabelValue S a (a (X ξ i)))
        (u (X ξ i) - S.level) := by
    rw [ae_all_iff]
    intro i
    exact ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact hsource)
  have hYs : ∀ᵐ ξ ∂sample, ∀ j : Fin n, ∀ c : Fin D.haar.continuous.count,
      a (Y ξ j) ∈ (D.haar.continuous.coefficient c).roots →
      let S := (P (D.haar.continuous.coefficient c).seedIndex).seed
      Y ξ j = S.curve (populationSeedRootLabelValue S a (a (Y ξ j)))
        (u (Y ξ j) - S.level) := by
    rw [ae_all_iff]
    intro j
    exact ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact htarget)
  filter_upwards [hXs, hYs] with ξ hx hy
  intro c i j hij
  have hxi := (T.partition c.1).cell_subset c.2 hij.1
  have hyj := (T.partition c.1).cell_subset c.2 hij.2.1
  exact ⟨(T.partition c.1).center_mem c.2, hxi, hyj, hij.2.2,
    hx i c.1 hxi.1, hy j c.1 hyj.1⟩

/-- All retained clipped frozen costs on their original disjoint edge events,
with zero cost off the retained events. -/
def originalFrozenCoreMatrix {n : ℕ} (X Y : Fin n → M) (scale t : ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  finiteTileSplice (fun c ↦ T.edgeEvent X Y c) (fun _ _ ↦ 0)
    (fun c ↦ frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c) X Y scale t (h c))

/-- Disjoint tile assembly retains the clipped cost of the actual occupied tile. -/
theorem originalFrozenCoreMatrix_on {n : ℕ} (X Y : Fin n → M) (scale t : ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) {c : T.Index} {i j : Fin n}
    (hij : (i, j) ∈ T.edgeEvent X Y c) :
    T.originalFrozenCoreMatrix X Y scale t h i j =
      frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c) X Y scale t (h c) i j :=
  finiteTileSplice_on _ _ _ (T.edgeEvent_disjoint X Y) hij

/-- The original frozen matrix vanishes outside all retained tile events. -/
theorem originalFrozenCoreMatrix_outside {n : ℕ} (X Y : Fin n → M) (scale t : ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hij : ∀ c, (i, j) ∉ T.edgeEvent X Y c) :
    T.originalFrozenCoreMatrix X Y scale t h i j = 0 :=
  finiteTileSplice_outside _ _ _ hij

/-- Every entry of the simultaneous original frozen matrix is nonnegative. -/
theorem originalFrozenCoreMatrix_nonneg {n : ℕ} (X Y : Fin n → M) (scale t : ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) :
    ∀ i j, 0 ≤ T.originalFrozenCoreMatrix X Y scale t h i j := by
  classical
  intro i j
  by_cases he : ∃ c, (i, j) ∈ T.edgeEvent X Y c
  · obtain ⟨c, hc⟩ := he
    rw [T.originalFrozenCoreMatrix_on X Y scale t h hc]
    exact frozenCoreMatrix_nonneg _ _ _ _ _ _ _ _ i j
  · rw [T.originalFrozenCoreMatrix_outside X Y scale t h (fun c hc ↦ he ⟨c, hc⟩)]

/-- The simultaneous matrix is exactly the sum of its masked tile matrices.
This identity retains the same fractional assignment for every summand. -/
theorem originalFrozenCoreMatrix_eq_sum {n : ℕ} (X Y : Fin n → M) (scale t : ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    T.originalFrozenCoreMatrix X Y scale t h i j =
      ∑ c : T.Index, maskedFrozenCost (T.edgeEvent X Y c)
        (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c) X Y scale t (h c)) i j := by
  classical
  simp only [originalFrozenCoreMatrix, finiteTileSplice, sub_zero, zero_add]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : (i, j) ∈ T.edgeEvent X Y c
  · simp only [ite_eq_left hc, maskedFrozenCost_apply_of_mem hc]
  · simp only [ite_eq_right hc, maskedFrozenCost_apply_of_not_mem hc]

/-- The cost of the same fractional assignment splits exactly into its tile
contributions. No separate tile optimizers are introduced. -/
theorem fractionalAssignmentCost_originalFrozenCoreMatrix_eq_sum {n : ℕ}
    (X Y : Fin n → M) (scale t : ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    fractionalAssignmentCost (T.originalFrozenCoreMatrix X Y scale t h) A =
      ∑ c : T.Index, fractionalAssignmentCost
        (maskedFrozenCost (T.edgeEvent X Y c)
          (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c) X Y scale t (h c))) A := by
  simp_rw [fractionalAssignmentCost, T.originalFrozenCoreMatrix_eq_sum, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ c : T.Index, ∑ j, A i j *
        maskedFrozenCost (T.edgeEvent X Y c)
          (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c) X Y scale t (h c)) i j :=
      Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- Original sample measurability gives measurable entries of the total frozen
core without a measurable selection of a tile or of an optimal assignment. -/
theorem measurable_originalFrozenCoreMatrix
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOriginalMeasMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    (scale t : ℝ) (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ c i j, Measurable (fun ξ ↦ h ξ c i j)) :
    ∀ i j, Measurable (fun ξ ↦ T.originalFrozenCoreMatrix (X ξ) (Y ξ) scale t (h ξ) i j) := by
  let _instOriginalMeasProofMetric : MetricSpace M := F.metricSpace
  let _instOriginalMeasProofProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instOriginalMeasProofPolish : PolishSpace M := inferInstance
  let _instOriginalMeasProofBorel : BorelSpace (ℚ → M) := inferInstance
  apply measurable_finiteTileSplice
    (fun ξ c ↦ T.edgeEvent (X ξ) (Y ξ) c) (fun _ _ _ ↦ 0)
    (fun ξ c ↦ frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
      (X ξ) (Y ξ) scale t (h ξ c))
    (T.measurable_edgeEvent hu ha X Y hX hY) (fun _ _ ↦ measurable_const)
  intro c i j
  exact (((T.core c).measurable_frozenPhysicalCost hF hcomplete hu ha hinj
    (measurable_const (a := T.reference c)) (hX i) (hY j)).const_mul scale |>.const_mul
      (1 - 2 * ε)).add ((hh c i j).const_mul t) |>.max measurable_const

/-- Dominate all disjoint geometric tiles at once, paying a single probe bound.
The actual Finsler distance and the original potential are used throughout. -/
theorem originalFrozenCoreMatrix_le_tilted_add
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOriginalDomMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {n : ℕ} (X Y : Fin n → M) {scale t probeError G : ℝ} (hscale : 0 ≤ scale)
    (g : Matrix (Fin n) (Fin n) ℝ) (h : T.Index → Matrix (Fin n) (Fin n) ℝ)
    (hgeom : ∀ c : T.Index, ∀ i j, (i, j) ∈ T.edgeEvent X Y c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) X Y i j)
    (hgh : ∀ c i j, (i, j) ∈ T.edgeEvent X Y c → |g i j - h c i j| ≤ probeError)
    (hg : ∀ i j, |g i j| ≤ G) (hprobe : probeError ≤ G) :
    ∀ i j, T.originalFrozenCoreMatrix X Y scale t h i j ≤
      scale * ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) +
        t * g i j + |t| * G := by
  let _instOriginalDomProofMetric : MetricSpace M := F.metricSpace
  let _instOriginalDomProofProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instOriginalDomProofPolish : PolishSpace M := inferInstance
  let _instOriginalDomProofBorel : BorelSpace (ℚ → M) := inferInstance
  intro i j
  by_cases he : ∃ c, (i, j) ∈ T.edgeEvent X Y c
  · obtain ⟨c, hc⟩ := he
    rw [T.originalFrozenCoreMatrix_on X Y scale t h hc]
    simpa only [core, distanceSlackEdgeCost, F.metricSpace_dist] using
      frozenCoreMatrix_le_slack_add_probeBound hF hcomplete hu ha hinj
        (T.cover c.1) hε hε1 F.metricSpace_dist (fun _ ↦ rfl) hu hscale
        (hgeom c) (hgh c) hg hprobe i j hc
  · rw [T.originalFrozenCoreMatrix_outside X Y scale t h (fun c hc ↦ he ⟨c, hc⟩)]
    have hs : 0 ≤ scale * distanceSlackEdgeCost X Y u i j :=
      mul_nonneg hscale (distanceSlackEdgeCost_nonneg X Y u hu i j)
    have hb : -(|t| * G) ≤ t * g i j :=
      (abs_le.mp (show |t * g i j| ≤ |t| * G by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg t))).1
    simpa only [distanceSlackEdgeCost, F.metricSpace_dist] using (show
      0 ≤ scale * distanceSlackEdgeCost X Y u i j + t * g i j + |t| * G by linarith)

/-- Every optimum of the original empirical problem controls the total retained
frozen core, with one additive probe error for the entire assignment. -/
theorem originalFrozenCore_div_le_pressure_add
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOriginalCostMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {n : ℕ} (hn : 0 < n) (X Y : Fin n → M) {scale t probeError G : ℝ}
    (hscale : 0 ≤ scale) (g : Matrix (Fin n) (Fin n) ℝ)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ)
    (hgeom : ∀ c : T.Index, ∀ i j, (i, j) ∈ T.edgeEvent X Y c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) X Y i j)
    (hgh : ∀ c i j, (i, j) ∈ T.edgeEvent X Y c → |g i j - h c i j| ≤ probeError)
    (hg : ∀ i j, |g i j| ≤ G) (hprobe : probeError ≤ G)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j ↦ scale * ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)))
      g t) A) :
    fractionalAssignmentCost (T.originalFrozenCoreMatrix X Y scale t h) A / (n : ℝ) ≤
      perturbedAssignmentValue
        (fun i j ↦ scale * ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)))
        g t / (n : ℝ) + |t| * G := by
  exact fractionalAssignmentCost_div_le_perturbedAssignmentValue_div_add hn hA
    (T.originalFrozenCoreMatrix_le_tilted_add hF hcomplete hu ha hinj hε hε1
      X Y hscale g h hgeom hgh hg hprobe)

/-- Original marginal laws supply a single full-measure event on which every
optimal fractional assignment controls the retained frozen core. The probe is
the same physical probe on every tile; no optimizer selection or geometric
edge hypothesis remains an input. -/
theorem ae_originalFrozenCore_div_le_pressure_add
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOriginalAeMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instOriginalAeOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} {n : ℕ} (hn : 0 < n)
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    (hXlaw : ∀ i, sample.map (fun ξ ↦ X ξ i) = η₀)
    (hYlaw : ∀ j, sample.map (fun ξ ↦ Y ξ j) = η₁)
    {scale t : ℝ} (hscale : 0 ≤ scale) (G : ℝ≥0)
    (g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ G) :
    ∀ᵐ ξ ∂sample, ∀ A : Matrix (Fin n) (Fin n) ℝ,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ scale *
          ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i)))
        (g ξ) t) A →
      fractionalAssignmentCost
          (T.originalFrozenCoreMatrix (X ξ) (Y ξ) scale t (fun _ ↦ g ξ)) A / (n : ℝ) ≤
        perturbedAssignmentValue
          (fun i j ↦ scale *
            ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i)))
          (g ξ) t / (n : ℝ) + |t| * (G : ℝ) := by
  have hgeom := T.ae_original_edge_geometry hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg X Y hX hY hXlaw hYlaw
  filter_upwards [hgeom, hg] with ξ hgeomξ hgξ
  intro A hA
  exact T.originalFrozenCore_div_le_pressure_add hF hcomplete hu ha hinj hε hε1
    hn (X ξ) (Y ξ) hscale (g ξ) (fun _ ↦ g ξ) hgeomξ
    (probeError := 0) (fun _ _ _ _ ↦ by simp) hgξ G.coe_nonneg hA

/-- The original-law bound feeds finite domination at every sample size, with
its actual sample-size-dependent scaling. All tiles use the same optimizer. -/
theorem original_finiteDominationInequality
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOriginalSequenceMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instOriginalSequenceOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω}
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    (X Y : ∀ n, Ω → Fin (N n) → M)
    (hX : ∀ n i, Measurable (fun ξ ↦ X n ξ i))
    (hY : ∀ n j, Measurable (fun ξ ↦ Y n ξ j))
    (hXlaw : ∀ n i, sample.map (fun ξ ↦ X n ξ i) = η₀)
    (hYlaw : ∀ n j, sample.map (fun ξ ↦ Y n ξ j) = η₁)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) (t : ℝ) (G : ℝ≥0)
    (g : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hg : ∀ n, ∀ᵐ ξ ∂sample, ∀ i j, |g n ξ i j| ≤ G)
    (A : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hA : ∀ n, ∀ᵐ ξ ∂sample, OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j ↦ scale n *
        ((F.lengthEDist (X n ξ i) (Y n ξ j)).toReal - u (Y n ξ j) + u (X n ξ i)))
      (g n ξ) t) (A n ξ)) :
    PointProcess.FiniteDominationInequality sample
      (fun n ξ ↦ fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (X n ξ) (Y n ξ) (scale n) t (fun _ ↦ g n ξ))
        (A n ξ) / (N n : ℝ))
      (fun n ξ ↦ perturbedAssignmentValue
        (fun i j ↦ scale n *
          ((F.lengthEDist (X n ξ i) (Y n ξ j)).toReal - u (Y n ξ j) + u (X n ξ i)))
        (g n ξ) t / (N n : ℝ)) (|t| * (G : ℝ)) := by
  apply PointProcess.finiteDominationInequality_of_ae_bound
  intro n
  have hbound := T.ae_originalFrozenCore_div_le_pressure_add hF hcomplete hu ha hinj
    horder hb hinv hη₀reg hη₁reg hε hε1 (hN n) (X n) (Y n) (hX n) (hY n)
    (hXlaw n) (hYlaw n) (hscale n) G (g n) (hg n) (t := t)
  filter_upwards [hbound, hA n] with ξ hξ hAξ
  exact hξ (A n ξ) hAξ

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
