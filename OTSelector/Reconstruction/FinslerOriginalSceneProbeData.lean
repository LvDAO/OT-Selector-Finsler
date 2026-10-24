import OTSelector.Reconstruction.FinslerOriginalTilePairRegularity
import OTSelector.Reconstruction.FinslerOriginalTileNormalization
import OTSelector.Reconstruction.FinslerOriginalFrozenCostSupBound

/-!
# Physical scene probe data of the deep tile lane

This module closes the probe data gaps left open in
`FinslerOriginalTilePairRegularity.lean` for the actual physical scene probe
family of the deep tile lane.

## The physical scene probe family

The probe matrix of the deep tile lane is an arbitrary test family
`hprobe : ((K x K) ->b R) -> R -> N -> Omega n -> T.Index -> Matrix ...`.
The physical scene supplies it as the bounded continuous carrier probe
`g : (K x K) ->b R` read at the physical sample pair `(X n i s, Y n j s)`
(`physicalSceneProbeMatrix`, the concrete base probe matrix of
`FinslerOriginalFrozenCostSupBound.lean`), optionally with the concrete tile
normalization of `FinslerOriginalTileNormalization.lean`
(`physicalSceneTileProbeMatrix`).

Its pair kernel is the same probe read at a pair of physical points and
extended by zero off the carrier:
`physicalSceneProbeKernel` (raw) and `physicalSceneTileProbeKernel`
(normalized).

## What is proved here

* `physicalSceneProbeMatrix_eq_kernel`, `physicalSceneTileProbeMatrix_eq_kernel`:
  condition (i) of the deep lane, `hprobePair`, for the physical probe family:
  the matrix entries are exactly the pair kernel at the physical sample pair.
* `measurable_physicalSceneProbeKernel`, `measurable_physicalSceneTileProbeKernel`:
  pointwise measurability of the physical probe pair kernels, from
  measurability of the carrier probe `g`.
* `measurable_probe_of_secondCountable`: a bounded continuous carrier probe is
  measurable as soon as the ambient manifold is second countable. This is the
  only structural input of the probe side; in the actual physical scene the
  compact carrier sits in a Finsler manifold, where second countability is a
  standard structural assumption.
* `physicalSceneProbeKernel_abs_le`, `physicalSceneTileProbeKernel_abs_le_norm`,
  `physicalSceneTileProbeKernel_t_mul_abs_le`: the uniform pointwise bound,
  using only the boundedness of the scene probe on the compact carrier:
  `|kernel p| <= ||g||`, and after the tile normalization
  `|t * kernel p| <= ||g|| / (n+1)`.
* `physicalSceneProbe_tilePairKernel_measurable`,
  `physicalSceneProbe_tilePairKernel_bound`: condition (ii) of the deep lane
  (measurability and uniform bound of the masked tile pair kernel) for the
  physical probe family, including the frozen-cost part through the concrete
  coefficient matrix of `FinslerCoefficientPressureFreezing.lean` and its
  continuity as used in `FinslerOriginalTilePairRegularity.lean`.
* `physicalSceneProbe_tilePairKernel_data`: the two conditions (ii) packaged.

## Exact remaining sub-gap

Pointwise measurability of the physical probe pair kernel needs measurability
of the carrier probe `g` on `K x K`. For a bounded continuous probe this is
automatic under `[SecondCountableTopology M]` (proved here as
`measurable_probe_of_secondCountable`); the abstract tile lane context keeps
only `MeasurableSpace`/`BorelSpace` data and does not assume second
countability, so the measurability results are stated with the second
countability hypothesis and the bound results are unconditional. The
frozen-cost side (coefficient matrix, its continuity, the mask and the mask
bound) is fully discharged in `FinslerOriginalTilePairRegularity.lean`.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

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
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-! ## The physical scene probe matrix of the deep tile lane -/

/-- **The base probe matrix of the physical scene probe family.**  The bounded
continuous carrier probe `g` read at the physical sample pair
`(X n i s, Y n j s)`; this is the concrete base probe matrix of the deep tile
lane. -/
noncomputable def physicalSceneProbeBase {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K) :
    ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  probeMatrixBase (Ω := Ω) (ι := ι) g X Y hX hY

/-- **The physical scene probe matrix** of the deep tile lane (the probe family
view of the base probe matrix). -/
noncomputable def physicalSceneProbeMatrix {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K) :
    ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ι →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun _ _ ↦ physicalSceneProbeBase g X Y hX hY

/-- The entries of the physical scene probe matrix are the probe read at the
physical sample pair, independently of the probe and tilt arguments. -/
theorem physicalSceneProbeMatrix_apply {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (c : ι)
    (i j : Fin (n + 1)) :
    physicalSceneProbeMatrix g X Y hX hY f t n s c i j =
      g (⟨X n i s, hX n i s⟩, ⟨Y n j s, hY n j s⟩) := rfl

/-- **The normalized physical scene probe matrix** of the tile lane: the
concrete tile probe normalization `tileProbe` applied to the base probe
matrix. -/
noncomputable def physicalSceneTileProbeMatrix {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K) :
    ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ι →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  tileProbe (K := K) (physicalSceneProbeBase g X Y hX hY)

/-- The entries of the normalized physical scene probe matrix are the
normalized probe read at the physical sample pair. -/
theorem physicalSceneTileProbeMatrix_apply {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (c : ι)
    (i j : Fin (n + 1)) :
    physicalSceneTileProbeMatrix g X Y hX hY f t n s c i j =
      (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) *
        g (⟨X n i s, hX n i s⟩, ⟨Y n j s, hY n j s⟩) := by
  simp only [physicalSceneTileProbeMatrix, tileProbe, physicalSceneProbeBase,
    probeMatrixBase, Matrix.smul_apply, smul_eq_mul]

/-! ## The physical scene probe pair kernels -/

/-- **The physical scene probe pair kernel**: the bounded continuous carrier
probe read at a pair of physical points, extended by zero off the carrier. -/
noncomputable def physicalSceneProbeKernel {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) : M × M → ℝ :=
  modelProbeKernel K g t n c

/-- **The normalized physical scene probe pair kernel** of the tile lane. -/
noncomputable def physicalSceneTileProbeKernel {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) : M × M → ℝ :=
  fun p ↦ (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) *
    physicalSceneProbeKernel g t n c p

/-- On the carrier the physical scene probe pair kernel is the original
bounded continuous probe. -/
theorem physicalSceneProbeKernel_apply_mem {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) {p : M × M} (hp : p ∈ K ×ˢ K) :
    physicalSceneProbeKernel g t n c p =
      g ((MeasurableEquiv.Set.prod K K) ⟨p, hp⟩) :=
  modelProbeKernel_apply_mem hp

/-- **The physical scene probe pair kernel is uniformly bounded** by the sup
norm of the carrier probe (boundedness of the scene probe on the compact
carrier). -/
theorem physicalSceneProbeKernel_abs_le {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) (p : M × M) :
    |physicalSceneProbeKernel g t n c p| ≤ ‖g‖ :=
  modelProbeKernel_abs_le p

/-- **Pointwise measurability of the physical scene probe pair kernel** from
measurability of the carrier probe. -/
theorem measurable_physicalSceneProbeKernel {ι : Type*} (hK : MeasurableSet K)
    (g : (K × K) →ᵇ ℝ) (hg : Measurable g) (t : ℝ) (n : ℕ) (c : ι) :
    Measurable (physicalSceneProbeKernel g t n c) :=
  measurable_modelProbeKernel hK g hg t n c

/-- On the carrier the normalized physical scene probe pair kernel is the
normalized probe read. -/
theorem physicalSceneTileProbeKernel_apply_mem {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) {p : M × M} (hp : p ∈ K ×ˢ K) :
    physicalSceneTileProbeKernel g t n c p =
      (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) *
        g ((MeasurableEquiv.Set.prod K K) ⟨p, hp⟩) := by
  rw [physicalSceneTileProbeKernel, physicalSceneProbeKernel_apply_mem g t n c hp]

/-- **The normalized physical scene probe pair kernel is bounded** by the
normalized sup norm of the carrier probe. -/
theorem physicalSceneTileProbeKernel_abs_le {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) (p : M × M) :
    |physicalSceneTileProbeKernel g t n c p| ≤
      (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * ‖g‖ := by
  have hc0 : 0 ≤ 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) := by positivity
  rw [physicalSceneTileProbeKernel, abs_mul, abs_of_nonneg hc0]
  exact mul_le_mul_of_nonneg_left (physicalSceneProbeKernel_abs_le g t n c p) hc0

/-- **Uniform pointwise bound of the normalized physical scene probe pair
kernel** by the sup norm of the carrier probe. -/
theorem physicalSceneTileProbeKernel_abs_le_norm {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) (p : M × M) :
    |physicalSceneTileProbeKernel g t n c p| ≤ ‖g‖ := by
  have hden : (1 : ℝ) ≤ (1 + |t|) * ((n + 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [abs_nonneg t])
    simpa using h
  have hpos : (0 : ℝ) < (1 + |t|) * ((n + 1 : ℕ) : ℝ) := by positivity
  have hcoef : 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one hpos]
    exact hden
  calc |physicalSceneTileProbeKernel g t n c p|
      ≤ (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * ‖g‖ :=
        physicalSceneTileProbeKernel_abs_le g t n c p
    _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg g)
    _ = ‖g‖ := one_mul _

/-- **The tilt times the normalized physical scene probe pair kernel is
uniformly O(1/(n+1))**, the probe normalization bound of the tile lane. -/
theorem physicalSceneTileProbeKernel_t_mul_abs_le {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) (p : M × M) :
    |t * physicalSceneTileProbeKernel g t n c p| ≤
      ‖g‖ / ((n + 1 : ℕ) : ℝ) := by
  have hpos1 : (0 : ℝ) < 1 + |t| := by positivity
  have hc0 : 0 ≤ 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) := by positivity
  have hcoef : |t| / (1 + |t|) ≤ 1 := by
    rw [div_le_one hpos1]
    linarith [le_abs_self t]
  have hscal : |t| * (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
    have hsplit : |t| * (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) =
        (|t| / (1 + |t|)) * (1 / ((n + 1 : ℕ) : ℝ)) := by
      field_simp
    rw [hsplit]
    calc (|t| / (1 + |t|)) * (1 / ((n + 1 : ℕ) : ℝ))
        ≤ 1 * (1 / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 1 / ((n + 1 : ℕ) : ℝ) := one_mul _
  calc |t * physicalSceneTileProbeKernel g t n c p|
      = |t| * ((1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) *
          |physicalSceneProbeKernel g t n c p|) := by
        rw [physicalSceneTileProbeKernel, abs_mul, abs_mul, abs_of_nonneg hc0]
    _ ≤ |t| * ((1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * ‖g‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (physicalSceneProbeKernel_abs_le g t n c p) hc0)
          (abs_nonneg t)
    _ = (|t| * (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)))) * ‖g‖ := by ring
    _ ≤ (1 / ((n + 1 : ℕ) : ℝ)) * ‖g‖ :=
        mul_le_mul_of_nonneg_right hscal (norm_nonneg g)
    _ = ‖g‖ / ((n + 1 : ℕ) : ℝ) := by ring

/-- **Pointwise measurability of the normalized physical scene probe pair
kernel.** -/
theorem measurable_physicalSceneTileProbeKernel {ι : Type*} (hK : MeasurableSet K)
    (g : (K × K) →ᵇ ℝ) (hg : Measurable g) (t : ℝ) (n : ℕ) (c : ι) :
    Measurable (physicalSceneTileProbeKernel g t n c) := by
  show Measurable (fun p : M × M ↦
    (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * physicalSceneProbeKernel g t n c p)
  exact Measurable.const_mul (measurable_physicalSceneProbeKernel hK g hg t n c) _

/-! ## Condition (i): the matrix entries are the pair kernel at the sample pair -/

/-- **Condition (i) of the deep lane for the physical scene probe family**: the
physical scene probe matrix entries are exactly the physical scene probe pair
kernel at the physical sample pair. -/
theorem physicalSceneProbeMatrix_eq_kernel {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (c : ι)
    (i j : Fin (n + 1)) :
    physicalSceneProbeMatrix g X Y hX hY f t n s c i j =
      physicalSceneProbeKernel g t n c (X n i s, Y n j s) := by
  rw [physicalSceneProbeMatrix_apply g X Y hX hY f t n s c i j,
    physicalSceneProbeKernel_apply_mem (p := (X n i s, Y n j s)) g t n c
      ⟨hX n i s, hY n j s⟩]
  rfl

/-- **Condition (i) of the deep lane for the normalized physical scene probe
family.** -/
theorem physicalSceneTileProbeMatrix_eq_kernel {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (c : ι)
    (i j : Fin (n + 1)) :
    physicalSceneTileProbeMatrix g X Y hX hY f t n s c i j =
      physicalSceneTileProbeKernel g t n c (X n i s, Y n j s) := by
  rw [physicalSceneTileProbeMatrix_apply g X Y hX hY f t n s c i j,
    physicalSceneTileProbeKernel_apply_mem (p := (X n i s, Y n j s)) g t n c
      ⟨hX n i s, hY n j s⟩]
  rfl

/-! ## Uniform bounds of the pair kernels -/

/-- **Uniform pointwise bound of the physical scene probe pair kernel.** -/
theorem physicalSceneProbeKernel_bound {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M, |physicalSceneProbeKernel g t n c p| ≤ B :=
  ⟨‖g‖, norm_nonneg g, fun p ↦ physicalSceneProbeKernel_abs_le g t n c p⟩

/-- **Uniform pointwise bound of the normalized physical scene probe pair
kernel.** -/
theorem physicalSceneTileProbeKernel_bound {ι : Type*} (g : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M, |physicalSceneTileProbeKernel g t n c p| ≤ B :=
  ⟨‖g‖, norm_nonneg g, fun p ↦ physicalSceneTileProbeKernel_abs_le_norm g t n c p⟩

/-! ## Structural measurability of the carrier probe -/

/-- **A bounded continuous carrier probe is measurable** as soon as the ambient
manifold is second countable. This is the only structural input needed for
pointwise measurability of the physical scene probe pair kernels; the physical
scene (a compact carrier in a Finsler manifold) satisfies it. -/
theorem measurable_probe_of_secondCountable [SecondCountableTopology M]
    (g : (K × K) →ᵇ ℝ) : Measurable g :=
  g.continuous.measurable

/-! ## Condition (ii) of the deep lane for the physical probe family -/

/-- **Condition (ii), measurability part, for the physical scene probe family**:
the masked tile pair kernel of every tile and every physical probe is
measurable. The frozen-cost and mask parts are those of
`FinslerOriginalTilePairRegularity.lean`; the probe part is the physical scene
probe pair kernel. -/
theorem physicalSceneProbe_tilePairKernel_measurable
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    [SecondCountableTopology M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPhysicalProbeMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (scale : ℕ → ℝ) :
    ∀ (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) := by
  intro g t n c
  exact tilePairKernel_measurable_of_probe (T := T) hF hcomplete hu ha hinj scale
    (physicalSceneTileProbeKernel (ι := T.Index))
    (fun g' t' n' c' ↦ measurable_physicalSceneTileProbeKernel hK g'
      (measurable_probe_of_secondCountable g') t' n' c') g t n c

/-- **Condition (ii), bound part, for the physical scene probe family**: the
masked tile pair kernel of every tile and every physical probe is uniformly
bounded. This is unconditional: the mask bound of
`FinslerOriginalTilePairRegularity.lean` plus the probe bound `||g||`. -/
theorem physicalSceneProbe_tilePairKernel_bound (scale : ℕ → ℝ)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
      |T.tilePairKernel c (scale n) t (physicalSceneTileProbeKernel g t n c) p| ≤ B :=
  tilePairKernel_bound_of_probe (T := T) scale
    (physicalSceneTileProbeKernel (ι := T.Index))
    (fun g' t' n' c' ↦ physicalSceneTileProbeKernel_bound g' t' n' c') g t n c

/-- **Condition (ii) of the deep lane, packaged for the physical scene probe
family**: for every physical probe, tile and tilt, the masked tile pair kernel
is measurable and uniformly bounded. -/
theorem physicalSceneProbe_tilePairKernel_data
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    [SecondCountableTopology M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPhysicalProbeDataMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (scale : ℕ → ℝ)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tilePairKernel c (scale n) t
          (physicalSceneTileProbeKernel g t n c) p| ≤ B :=
  ⟨physicalSceneProbe_tilePairKernel_measurable (T := T) hF hcomplete hu ha hinj
      hK scale g t n c,
    physicalSceneProbe_tilePairKernel_bound (T := T) scale g t n c⟩

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction

