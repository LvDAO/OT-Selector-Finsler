import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Compactness.Compact

/-!
# Analysis.Calculus.AffineEndpointVariation

Conditions: A nondegenerate real interval, an actual C1 path and open admissible phase domain around its compact trace, with the explicit endpoint displacements.

Objects: Affine endpoint perturbation, its phase/derivative/endpoints, and one admissible perturbation strip.

Proof detail: Interpolate endpoint displacements affinely, differentiate the explicit expression, and use compactness of the central phase trace inside the open domain to choose one common strip.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation: Classical affine variation and a local compact-open corollary; no Euler–Lagrange stationarity assertion is made here.
-/

/-!
# Actual smooth endpoint variations inside a compact slit phase trace

An affine-in-time endpoint perturbation keeps the initial endpoint fixed and moves the
terminal endpoint to the prescribed parameter. Its actual time derivative is computed.
An open phase domain containing the compact central trace supplies a common open strip
on which every varied position and actual velocity remain in that same domain.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vary the terminal endpoint of the actual coordinate path, leaving its initial point fixed. -/
def affineEndpointVariation (x : ℝ → E) (a b : ℝ) (p : E × ℝ) : E :=
  x p.2 + ((p.2 - a) / (b - a)) • (p.1 - x b)

/-- The actual position and computed time velocity of the endpoint variation. -/
def affineEndpointPhase (x : ℝ → E) (a b : ℝ) (p : E × ℝ) : E × E :=
  (affineEndpointVariation x a b p, deriv x p.2 + (b - a)⁻¹ • (p.1 - x b))

/-- The central parameter recovers the original path and its actual velocity. -/
theorem affineEndpointPhase_center (x : ℝ → E) (a b t : ℝ) :
    affineEndpointPhase x a b (x b, t) = (x t, deriv x t) := by
  simp [affineEndpointPhase, affineEndpointVariation]

/-- The varied path has the original initial endpoint and the prescribed final endpoint. -/
theorem affineEndpointVariation_endpoints (x : ℝ → E) {a b : ℝ} (hab : a < b) (z : E) :
    affineEndpointVariation x a b (z, a) = x a ∧
      affineEndpointVariation x a b (z, b) = z := by
  simp [affineEndpointVariation, (sub_pos.mpr hab).ne']

/-- The phase velocity is the actual derivative of the varied coordinate path. -/
theorem hasDerivAt_affineEndpointVariation {x : ℝ → E} {a b t : ℝ}
    (hx : DifferentiableAt ℝ x t) (z : E) :
    HasDerivAt (fun s ↦ affineEndpointVariation x a b (z, s))
      (affineEndpointPhase x a b (z, t)).2 t := by
  have hlinear : HasDerivAt (fun s : ℝ ↦ s - a) 1 t := (hasDerivAt_id t).sub_const a
  have h := HasDerivAt.fun_add hx.hasDerivAt
    ((hlinear.div_const (b - a)).smul_const (z - x b))
  simpa only [affineEndpointVariation, affineEndpointPhase, one_div, Pi.add_apply] using h

/-- The actual varied position is jointly smooth in endpoint and time. -/
theorem contDiffOn_affineEndpointVariation {x : ℝ → E} {I : Set ℝ}
    (hx : ContDiffOn ℝ ∞ x I) (a b : ℝ) :
    ContDiffOn ℝ ∞ (affineEndpointVariation x a b) (univ ×ˢ I) := by
  have hxt : ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ x p.2) (univ ×ˢ I) :=
    hx.comp contDiffOn_snd (fun _ hp ↦ hp.2)
  exact hxt.add (((contDiffOn_snd.sub contDiffOn_const).div_const (b - a)).smul
    (contDiffOn_fst.sub contDiffOn_const))

/-- The actual phase is jointly smooth wherever the central path is smooth on an open interval. -/
theorem contDiffOn_affineEndpointPhase {x : ℝ → E} {I : Set ℝ}
    (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I) (a b : ℝ) :
    ContDiffOn ℝ ∞ (affineEndpointPhase x a b) (univ ×ˢ I) := by
  have hd : ContDiffOn ℝ ∞ (deriv x) I :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hI).mp hx).2
  have hdt : ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ deriv x p.2) (univ ×ˢ I) :=
    hd.comp contDiffOn_snd (fun _ hp ↦ hp.2)
  exact (contDiffOn_affineEndpointVariation hx a b).prodMk
    (hdt.add (contDiffOn_const.smul (contDiffOn_fst.sub contDiffOn_const)))

/-- Compactness constructs one open endpoint-time strip staying in the actual phase domain.
In particular an original slit trace gives nonzero actual velocities throughout this strip. -/
theorem exists_affineEndpointVariation_strip {x : ℝ → E} {I : Set ℝ}
    (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I) {a b : ℝ}
    (hseg : Icc a b ⊆ I) {D : Set (E × E)} (hD : IsOpen D)
    (htrace : ∀ t ∈ Icc a b, (x t, deriv x t) ∈ D) :
    ∃ U : Set E, ∃ V : Set ℝ, IsOpen U ∧ x b ∈ U ∧ IsOpen V ∧
      Icc a b ⊆ V ∧ V ⊆ I ∧ MapsTo (affineEndpointPhase x a b) (U ×ˢ V) D := by
  let O := (univ ×ˢ I) ∩ (affineEndpointPhase x a b) ⁻¹' D
  have hO : IsOpen O :=
    (contDiffOn_affineEndpointPhase hI hx a b).continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod hI) hD
  have hcentral : ({x b} : Set E) ×ˢ Icc a b ⊆ O := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have heq : z = x b := hz
    subst z
    refine ⟨⟨mem_univ _, hseg ht⟩, ?_⟩
    change affineEndpointPhase x a b (x b, t) ∈ D
    simpa only [affineEndpointPhase_center] using htrace t ht
  obtain ⟨U, V, hU, hV, hpoint, hinterval, hstrip⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hO hcentral
  refine ⟨U, V ∩ I, hU, hpoint (mem_singleton _), hV.inter hI,
    fun t ht ↦ ⟨hinterval ht, hseg ht⟩, inter_subset_right, ?_⟩
  intro p hp
  exact (hstrip ⟨hp.1, hp.2.1⟩).2

end OTSelector.Geometry
