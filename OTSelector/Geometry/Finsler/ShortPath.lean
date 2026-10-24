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

/-!
## Lemma skeleton

* **Conditions:** A C1 curve and a neighborhood containing a ball for the genuine Finsler length distance; its length is shorter than the radius. For the final comparison, a domain-local minimizing property or supplied calibration.
* **Objects:** Containment of short curves and equality of actual length distance with the short locally minimizing reference length.
* **Proof detail:** Bound every prefix distance by total length. Any hypothetical shorter competitor stays inside the local comparison domain, contradicting local minimality; calibrated minimality supplies that comparison.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Anton Petrunin, *Lectures on metric geometry (author lecture notes, course Spring 2020)*, Lecture 1, Section L, pp. 16–17: length spaces, induced length metric and approximate midpoints.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=16
* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22

**Relationship to the sources:** Elementary localization of the induced-length infimum and one-dimensional calibration argument. The radius/domain hypotheses remain explicit.
-/

/-!
# Short curves stay in a length ball

Prefix length bounds imply that a sufficiently short C1 curve remains in a prescribed
neighborhood containing a ball for the original Finsler length distance. This removes the
domain-containment restriction from a local length comparison when the reference is shorter
than the radius. All path lengths use exactly the given `ContinuousFinslerNorm.enorm`.

The distance-ball containment and the local comparison (or an actual calibration) are explicit
inputs. This module does not construct a calibration or assert unconditional geodesic minimality.
-/

open Bundle Set Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- Every point of a C1 curve is at most its total original Finsler length from its start. -/
theorem lengthEDist_le_pathELength_of_mem_Icc (F : ContinuousFinslerNorm E M)
    {c : ℝ → M} {a b t : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b)) (ht : t ∈ Icc a b) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (c a) (c t) ≤ Manifold.pathELength 𝓘(ℝ, E) c a b := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let : ∀ x : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := F.enormSMulClass
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a t) :=
    hc.mono (Icc_subset_Icc le_rfl ht.2)
  exact (Manifold.riemannianEDist_le_pathELength hp rfl rfl ht.1).trans
    (Manifold.pathELength_mono le_rfl ht.2)

/-- A curve shorter than a length-ball radius stays in every set containing that ball.
No nonzero-speed assumption or ordinary derivative at an endpoint is needed. -/
theorem mapsTo_of_pathELength_lt (F : ContinuousFinslerNorm E M)
    {U : Set M} {x : M} {ε : ℝ≥0∞}
    (hball : {y | F.lengthEDist x y < ε} ⊆ U)
    {c : ℝ → M} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b)) (hstart : c a = x)
    (hlen : letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
      Manifold.pathELength 𝓘(ℝ, E) c a b < ε) :
    MapsTo c (Icc a b) U := by
  intro t ht
  apply hball
  rw [← hstart]
  exact (F.lengthEDist_le_pathELength_of_mem_Icc hc ht).trans_lt hlen

/-- A sufficiently short locally minimizing curve realizes the original Finsler length distance.
It suffices to compare with all domain-contained C1 competitors on [0,1], the parameter interval
used in the definition of the distance infimum. -/
theorem lengthEDist_eq_pathELength_of_local_minimal (F : ContinuousFinslerNorm E M)
    {U : Set M} {c : ℝ → M} {a b : ℝ} {ε : ℝ≥0∞}
    (hab : a ≤ b) (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hball : {y | F.lengthEDist (c a) y < ε} ⊆ U)
    (hlen : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      Manifold.pathELength 𝓘(ℝ, E) c a b < ε)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ d : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 d (Icc 0 1) →
        d 0 = c a → d 1 = c b → MapsTo d (Icc 0 1) U →
          Manifold.pathELength 𝓘(ℝ, E) c a b ≤ Manifold.pathELength 𝓘(ℝ, E) d 0 1) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (c a) (c b) = Manifold.pathELength 𝓘(ℝ, E) c a b := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let : ∀ x : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := F.enormSMulClass
  apply le_antisymm
  · exact Manifold.riemannianEDist_le_pathELength hc rfl rfl hab
  · apply le_of_not_gt
    intro hdist
    obtain ⟨d, hd0, hd1, hd, hdlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hdist
    have hdmap : MapsTo d (Icc 0 1) U :=
      F.mapsTo_of_pathELength_lt hball hd hd0 (hdlen.trans hlen)
    exact (not_lt_of_ge (hmin d hd hd0 hd1 hdmap)) hdlen

/-- A calibrated curve shorter than a contained length-ball radius realizes the genuine
Finsler length distance. Shortness also derives containment of the reference curve itself. -/
theorem lengthEDist_eq_pathELength_of_calibrated (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x v) (F.toFun ⟨x, v⟩ : ℝ))
    {c : ℝ → M} {a b : ℝ} {ε : ℝ≥0∞} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hball : {y | F.lengthEDist (c a) y < ε} ⊆ U)
    (hlen : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      Manifold.pathELength 𝓘(ℝ, E) c a b < ε)
    (hsat : ∀ t ∈ Ioo a b,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1) =
          (F.toFun ⟨c t, mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1⟩ : ℝ)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (c a) (c b) = Manifold.pathELength 𝓘(ℝ, E) c a b := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hcmap : MapsTo c (Icc a b) U := F.mapsTo_of_pathELength_lt hball hc rfl hlen
  apply F.lengthEDist_eq_pathELength_of_local_minimal hab hc hball hlen
  intro d hd hd0 hd1 hdmap
  exact F.pathELength_le_of_calibrated hU hu hbound hab zero_le_one hc hd hcmap hdmap
    hd0.symm hd1.symm hsat

end OTSelector.Geometry.ContinuousFinslerNorm
