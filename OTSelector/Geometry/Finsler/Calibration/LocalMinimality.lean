import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.ShortPath

/-!
## Lemma skeleton

* **Conditions:** A C1 manifold potential satisfying du(v) ≤ F(v) and a C1 saturated curve in its open domain; finite-dimensional regular manifold only to construct the local distance neighborhood.
* **Objects:** An exact length–potential-increment formula and a positive time neighborhood on which every ordered subsegment realizes the genuine length distance.
* **Proof detail:** Apply the chain rule and FTC for the saturated integral. Use continuity of the potential and curve to obtain short segments and a contained length ball, then exclude shorter competitors.

## Mathematical sources

* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** One-dimensional exact-potential specialization and local-domain version of calibration minimality. C1 regularity and the explicit short-path exit handling are proved here.
-/

/-!
# Local distance realization by calibrated curves

A C1 curve saturated by a C1 calibration realizes the original Finsler length
distance between any two ordered times in a sufficiently small closed time interval.
The time radius, a contained length ball, and the required shortness are derived
from the given open domains and continuity. Saturation uses the ordinary manifold
derivative; the closed-segment comparison handles endpoints internally.

The calibration and its differential bound are explicit inputs. This module does
not construct a calibration or assume nonzero speed, curvature, or an inner product.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- Ordinary differential saturation suffices for the actual closed-segment length formula. -/
theorem pathELength_eq_of_calibrated_mfderiv (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hmap : MapsTo c (Icc a b) U)
    (hsat : ∀ t ∈ Ioo a b,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) =
        (F.toFun ⟨c t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1⟩ : ℝ)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    Manifold.pathELength 𝓘(ℝ, E) c a b = ENNReal.ofReal (u (c b) - u (c a)) := by
  apply F.pathELength_eq_of_calibrated hU hu hab hc hmap
  intro t ht
  rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  exact hsat t ht

/-- A calibrated curve realizes the true Finsler length distance for every ordered pair of
times in a positive closed neighborhood of the reference time. All required shortness and
length-ball containment are constructed from continuity and the original open domains. -/
theorem exists_local_minimality_of_calibrated [FiniteDimensional ℝ E] [RegularSpace M]
    (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x v) (F.toFun ⟨x, v⟩ : ℝ))
    {c : ℝ → M} {S : Set ℝ} {t₀ : ℝ} (hS : IsOpen S) (ht₀ : t₀ ∈ S)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c S) (hmap : MapsTo c S U)
    (hsat : ∀ t ∈ S,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) =
        (F.toFun ⟨c t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1⟩ : ℝ)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ δ : ℝ, 0 < δ ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ S ∧
      ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), s ≤ t →
        F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨R, hR, hball⟩ := F.lengthEDist_ball_subset_nhds (hU.mem_nhds (hmap ht₀))
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  let ε : ℝ≥0 := R / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεE : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hcAt : ContinuousAt c t₀ := hc.continuousOn.continuousAt (hS.mem_nhds ht₀)
  have huAt : ContinuousAt (fun t ↦ u (c t)) t₀ :=
    (hu.continuousOn.continuousAt (hU.mem_nhds (hmap ht₀))).comp hcAt
  have hdist : ∀ᶠ t in 𝓝 t₀, F.lengthEDist (c t₀) (c t) < ε :=
    hcAt (F.eventually_lengthEDist_lt (c t₀) hεE)
  have hpotential : ∀ᶠ t in 𝓝 t₀, |u (c t) - u (c t₀)| < (R : ℝ) / 4 := by
    have h : ∀ᶠ t in 𝓝 t₀, u (c t) ∈ ball (u (c t₀)) ((R : ℝ) / 4) :=
      huAt (ball_mem_nhds (u (c t₀)) (by positivity : 0 < (R : ℝ) / 4))
    simpa only [mem_ball, Real.dist_eq] using h
  obtain ⟨δ, hδ, hδgood⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hS.mem_nhds ht₀) (inter_mem hdist hpotential))
  have hwindow : Icc (t₀ - δ) (t₀ + δ) ⊆ closedBall t₀ δ := by
    intro t ht
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hwindowS : Icc (t₀ - δ) (t₀ + δ) ⊆ S := fun _ ht ↦
    (hδgood (hwindow ht)).1
  refine ⟨δ, hδ, hwindowS, ?_⟩
  intro s hs t ht hst
  have hseg : Icc s t ⊆ S :=
    (Icc_subset_Icc hs.1 ht.2).trans hwindowS
  have hcseg := hc.mono hseg
  have hmapseg : MapsTo c (Icc s t) U := fun _ hx ↦ hmap (hseg hx)
  have hsatseg : ∀ q ∈ Ioo s t,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c q)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc s t) q 1) =
          (F.toFun ⟨c q, mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc s t) q 1⟩ : ℝ) := by
    intro q hq
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds hq.1 hq.2)]
    exact hsat q (hseg (Ioo_subset_Icc_self hq))
  have hlength := F.pathELength_eq_of_calibrated hU hu hst hcseg hmapseg hsatseg
  have hshort : Manifold.pathELength 𝓘(ℝ, E) c s t < (ε : ℝ≥0∞) := by
    rw [hlength, ← ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hε)).2
    have hsPot : |u (c s) - u (c t₀)| < (R : ℝ) / 4 := (hδgood (hwindow hs)).2.2
    have htPot : |u (c t) - u (c t₀)| < (R : ℝ) / 4 := (hδgood (hwindow ht)).2.2
    change u (c t) - u (c s) < (R : ℝ) / 2
    linarith [(abs_lt.mp hsPot).1, (abs_lt.mp htPot).2]
  have hball_s : {y | F.lengthEDist (c s) y < (ε : ℝ≥0∞)} ⊆ U := by
    intro y hy
    apply hball
    have hsDist : F.lengthEDist (c t₀) (c s) < ε := (hδgood (hwindow hs)).2.1
    have hsum : (ε : ℝ≥0∞) + ε = R := by
      rw [← ENNReal.coe_add]
      congr 1
      exact add_halves R
    exact (F.lengthEDist_triangle (c t₀) (c s) y).trans_lt
      (hsum ▸ ENNReal.add_lt_add hsDist hy)
  exact F.lengthEDist_eq_pathELength_of_calibrated hU hu hbound hst hcseg
    hball_s hshort hsatseg

end OTSelector.Geometry.ContinuousFinslerNorm
