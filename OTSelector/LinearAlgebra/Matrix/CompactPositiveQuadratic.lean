import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# LinearAlgebra.Matrix.CompactPositiveQuadratic

## Lemma skeleton

* **Conditions:** A continuous positive-definite finite real matrix field on a compact parameter set; the relative-freezing conclusion supplies a positive error tolerance.

* **Objects:** A uniform positive quadratic lower bound, relative quadratic freezing and a finite relative-error cover.

* **Proof detail:** Minimize the quadratic form on the compact parameter×unit-sphere set. Uniform continuity on that set bounds nearby quadratic differences absolutely; divide by the positive minimum and use degree-two homogeneity to treat all vectors. Extract a finite open cover.

## Mathematical sources

- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660): Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html): Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).

Source relation (corollary): Locally derived compact-sphere freezing estimates; no uniform spectral lower bound is inserted as an independent premise.
-/

/-!
# Relative freezing of compact positive quadratic coefficients

A continuous positive definite matrix field on a compact set has a uniform
quadratic lower bound. Uniform continuity on the unit sphere then gives relative
quadratic errors for all displacements, with constants produced from the field.
-/

open Set Matrix
open scoped Topology Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n]

/-- The actual quadratic coefficient convention, including the Taylor factor one half. -/
def matrixQuadratic (A : Matrix n n ℝ) (v : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v))

@[simp] theorem matrixQuadratic_zero (A : Matrix n n ℝ) : matrixQuadratic A 0 = 0 := by
  simp [matrixQuadratic]

/-- Quadratic scaling in the displacement keeps the original matrix fixed. -/
theorem matrixQuadratic_smul (A : Matrix n n ℝ) (r : ℝ) (v : n → ℝ) :
    matrixQuadratic A (r • v) = r ^ 2 * matrixQuadratic A v := by
  simp only [matrixQuadratic, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Strict positivity away from the zero displacement. -/
theorem matrixQuadratic_pos {A : Matrix n n ℝ} (hA : A.PosDef) {v : n → ℝ}
    (hv : v ≠ 0) : 0 < matrixQuadratic A v := by
  have h := hA.dotProduct_mulVec_pos hv
  simp only [star_trivial] at h
  exact mul_pos (by norm_num) h

/-- Joint continuity of the quadratic evaluation in coefficient and displacement. -/
theorem continuous_matrixQuadratic :
    Continuous (fun p : Matrix n n ℝ × (n → ℝ) ↦ matrixQuadratic p.1 p.2) := by
  unfold matrixQuadratic dotProduct Matrix.mulVec
  fun_prop

/-- The quadratic evaluation stays continuous when the matrix field is only continuous
on its compact parameter set. -/
theorem continuousOn_matrixQuadratic_field {Θ : Type*} [TopologicalSpace Θ]
    {K : Set Θ} {A : Θ → Matrix n n ℝ} (hA : ContinuousOn A K) (V : Set (n → ℝ)) :
    ContinuousOn (fun p : Θ × (n → ℝ) ↦ matrixQuadratic (A p.1) p.2) (K ×ˢ V) := by
  have hprod : ContinuousOn (fun p : Θ × (n → ℝ) ↦ (A p.1, p.2)) (K ×ˢ V) :=
    (hA.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)).prodMk
      continuous_snd.continuousOn
  exact continuous_matrixQuadratic.comp_continuousOn hprod

/-- Compact positive definite coefficients have a uniform strictly positive lower bound
for the quadratic form in the fixed vector norm. No lower bound is supplied as input. -/
theorem exists_uniform_matrixQuadratic_lower_bound {Θ : Type*} [TopologicalSpace Θ]
    {K : Set Θ} (hK : IsCompact K) {A : Θ → Matrix n n ℝ}
    (hA : ContinuousOn A K) (hpos : ∀ θ ∈ K, (A θ).PosDef) :
    ∃ m > 0, ∀ θ ∈ K, ∀ v : n → ℝ, m * ‖v‖ ^ 2 ≤ matrixQuadratic (A θ) v := by
  have hcompact := hK.prod (isCompact_sphere (0 : n → ℝ) 1)
  obtain ⟨m, hm, hmin⟩ := hcompact.exists_forall_le'
    (continuousOn_matrixQuadratic_field hA (Metric.sphere 0 1)) (a := (0 : ℝ)) (by
      intro p hp
      apply matrixQuadratic_pos (hpos p.1 hp.1)
      intro hz
      simpa [hz] using hp.2)
  refine ⟨m, hm, fun θ hθ v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let y : n → ℝ := ‖v‖⁻¹ • v
  have hy : y ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [y, norm_smul, ne_of_gt hvnorm]
  have hscale : ‖v‖ • y = v := by
    simp [y, smul_smul, ne_of_gt hvnorm]
  calc
    m * ‖v‖ ^ 2 = ‖v‖ ^ 2 * m := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * matrixQuadratic (A θ) y :=
      mul_le_mul_of_nonneg_left (hmin (θ, y) ⟨hθ, hy⟩) (sq_nonneg _)
    _ = matrixQuadratic (A θ) (‖v‖ • y) := (matrixQuadratic_smul _ _ _).symm
    _ = matrixQuadratic (A θ) v := by rw [hscale]

/-- Nearby coefficients on a compact positive definite field give uniformly relative
quadratic errors, valid for every displacement including arbitrarily large ones. -/
theorem exists_uniform_relative_matrixQuadratic {Θ : Type*} [PseudoMetricSpace Θ]
    {K : Set Θ} (hK : IsCompact K) {A : Θ → Matrix n n ℝ}
    (hA : ContinuousOn A K) (hpos : ∀ θ ∈ K, (A θ).PosDef)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ ∈ K, ∀ θ₀ ∈ K, dist θ θ₀ < δ → ∀ v : n → ℝ,
      |matrixQuadratic (A θ) v - matrixQuadratic (A θ₀) v| ≤
        ε * matrixQuadratic (A θ₀) v := by
  obtain ⟨m, hm, hmin⟩ := exists_uniform_matrixQuadratic_lower_bound hK hA hpos
  have hcompact := hK.prod (isCompact_sphere (0 : n → ℝ) 1)
  have huc := hcompact.uniformContinuousOn_of_continuous
    (continuousOn_matrixQuadratic_field hA (Metric.sphere 0 1))
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc (ε * m) (mul_pos hε hm)
  refine ⟨δ, hδ, fun θ hθ θ₀ hθ₀ hdist v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let y : n → ℝ := ‖v‖⁻¹ • v
  have hy : y ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [y, norm_smul, ne_of_gt hvnorm]
  have hynorm : ‖y‖ = 1 := by simpa using hy
  have hscale : ‖v‖ • y = v := by
    simp [y, smul_smul, ne_of_gt hvnorm]
  have hnear : dist (θ, y) (θ₀, y) < δ := by simpa [Prod.dist_eq] using hdist
  have hd := hclose (θ, y) ⟨hθ, hy⟩ (θ₀, y) ⟨hθ₀, hy⟩ hnear
  rw [Real.dist_eq] at hd
  have hmle : m ≤ matrixQuadratic (A θ₀) y := by simpa [hynorm] using hmin θ₀ hθ₀ y
  have hq (x : Θ) : matrixQuadratic (A x) v =
      ‖v‖ ^ 2 * matrixQuadratic (A x) y := by
    calc
      matrixQuadratic (A x) v = matrixQuadratic (A x) (‖v‖ • y) :=
        congrArg (matrixQuadratic (A x)) hscale.symm
      _ = _ := matrixQuadratic_smul _ _ _
  calc
    |matrixQuadratic (A θ) v - matrixQuadratic (A θ₀) v| =
        ‖v‖ ^ 2 * |matrixQuadratic (A θ) y - matrixQuadratic (A θ₀) y| := by
      rw [hq θ, hq θ₀, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖v‖ ^ 2 * (ε * m) := mul_le_mul_of_nonneg_left hd.le (sq_nonneg _)
    _ ≤ ‖v‖ ^ 2 * (ε * matrixQuadratic (A θ₀) y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmle hε.le) (sq_nonneg _)
    _ = ε * matrixQuadratic (A θ₀) v := by
      rw [hq θ₀]
      ring

/-- A compact parameter family admits finitely many open root neighborhoods on which
one original root coefficient approximates every coefficient relatively, simultaneously
for all marks in the compact mark region and every displacement. -/
theorem exists_finite_relative_matrixQuadratic_cover
    {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    {K : Set Z} {H : Set T} (hK : IsCompact K) (hH : IsCompact H)
    {A : Z × T → Matrix n n ℝ} (hA : ContinuousOn A (K ×ˢ H))
    (hpos : ∀ z ∈ K, ∀ p ∈ H, (A (z, p)).PosDef)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (centers : Set Z) (U : Z → Set Z), centers.Finite ∧ centers ⊆ K ∧
      K ⊆ ⋃ z ∈ centers, U z ∧ ∀ z₀ ∈ centers, IsOpen (U z₀) ∧ z₀ ∈ U z₀ ∧
        ∀ z ∈ K ∩ U z₀, ∀ p ∈ H, ∀ v : n → ℝ,
          |matrixQuadratic (A (z, p)) v - matrixQuadratic (A (z₀, p)) v| ≤
            ε * matrixQuadratic (A (z₀, p)) v := by
  let : MetricSpace Z := TopologicalSpace.metrizableSpaceMetric Z
  let : MetricSpace T := TopologicalSpace.metrizableSpaceMetric T
  obtain ⟨δ, hδ, hclose⟩ := exists_uniform_relative_matrixQuadratic
    (hK.prod hH) hA (fun q hq ↦ hpos q.1 hq.1 q.2 hq.2) hε
  let U : Z → Set Z := fun z ↦ Metric.ball z δ
  have hcover : K ⊆ ⋃ z ∈ K, U z := fun z hz ↦
    mem_iUnion_of_mem z (mem_iUnion_of_mem hz (Metric.mem_ball_self hδ))
  obtain ⟨centers, hsub, hfinite, hcov⟩ := hK.elim_finite_subcover_image
    (fun z _ ↦ Metric.isOpen_ball (x := z) (ε := δ)) hcover
  refine ⟨centers, U, hfinite, hsub, hcov, fun z₀ hz₀ ↦
    ⟨Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩⟩
  intro z hz p hp v
  apply hclose (z, p) ⟨hz.1, hp⟩ (z₀, p) ⟨hsub hz₀, hp⟩
  simpa [U, Metric.mem_ball, Prod.dist_eq] using hz.2

end OTSelector.Reconstruction
