import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.AffineCalibrationTube
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.ChartLipschitzCalibration
import OTSelector.Geometry.Finsler.EndpointDistanceBranch
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FamilyFrechetFirstVariation
import OTSelector.Geometry.Finsler.FlatBaseEndpoint
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.EndpointDistanceC3

* **Conditions:** The actual minimizing endpoint branch and jointly C2 tangent data for that same family.
* **Objects:** Original endpoint-distance differential given by actual length momenta and C3 regularity of the distance on the branch.
* **Proof detail:** Apply Frechet endpoint first variation to the proved distance–length identity, show its true momentum differential is C2 and upgrade distance regularity by one order.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): The result applies on the constructed branch; it does not assert smoothness at arbitrary cut-locus pairs.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointDistanceC3.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointDistanceC3`; the selected original proof blocks follow. -/
section

/-!
# Actual endpoint distance: gradient and C3 regularity

The same endpoint inverse branch of the complete Finsler family gives the actual
endpoint length momenta. Original first variation identifies the derivative of the
original global distance, and joint C2 tangent regularity makes this derivative C2.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- Actual position and velocity in the chosen chart on the same endpoint branch. -/
def endpointChartPhase (old : M) (Γ : (E × E) → ℝ → M)
    (e : OpenPartialHomeomorph (E × E) (E × E)) (t : ℝ) (q : E × E) : E × E :=
  ((extChartAt 𝓘(ℝ, E) old ∘ Γ (e.symm q)) t,
    deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ (e.symm q)) t)

/-- Actual length momentum at time `t` of the same endpoint-inverse branch. -/
def endpointLengthMomentum (F : ContinuousFinslerNorm E M) (old : M)
    (Γ : (E × E) → ℝ → M) (e : OpenPartialHomeomorph (E × E) (E × E))
    (t : ℝ) (q : E × E) : E →L[ℝ] ℝ :=
  fiberLegendre (fun z ↦ (F.chartLength old z : ℝ))
    (endpointChartPhase old Γ e t q)

/-- Final length momentum minus initial length momentum, on the two endpoint directions. -/
def endpointLengthDifferential (F : ContinuousFinslerNorm E M) (old : M)
    (Γ : (E × E) → ℝ → M) (e : OpenPartialHomeomorph (E × E) (E × E))
    (a b : ℝ) (q : E × E) : (E × E) →L[ℝ] ℝ :=
  (F.endpointLengthMomentum old Γ e b q).comp (ContinuousLinearMap.snd ℝ E E) -
    (F.endpointLengthMomentum old Γ e a q).comp (ContinuousLinearMap.fst ℝ E E)

namespace IsSmoothStronglyConvex

/-- Endpoint phase C2 regularity comes from the actual total tangent family. -/
theorem contDiffOn_endpointChartPhase (hF : F.IsSmoothStronglyConvex) (old : M)
    {Γ : (E × E) → ℝ → M} {e : OpenPartialHomeomorph (E × E) (E × E)}
    {W : Set (E × E)} {I : Set ℝ}
    (hEL : ∀ q ∈ W, F.IsEulerLagrangeOn (Γ (e.symm q)) I)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ (e.symm r.1))
        ⟨r.2, (1 : ℝ)⟩) (W ×ˢ I))
    (hmap : ∀ q ∈ W, MapsTo (Γ (e.symm q)) I (extChartAt 𝓘(ℝ, E) old).source)
    {t : ℝ} (ht : t ∈ I) : ContDiffOn ℝ 2 (endpointChartPhase old Γ e t) W := by
  have hphase := hF.contDiffOn_chartPhase_of_tangentFamily_C2 old
    (Γ := fun q ↦ Γ (e.symm q)) (D := W ×ˢ I)
    (fun r hr ↦ hEL r.1 hr.1 r.2 hr.2) hG (fun r hr ↦ hmap r.1 hr.1 hr.2)
  exact hphase.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hq ↦ ⟨hq, ht⟩)

/-- On an actual minimizing branch, first variation gives its endpoint gradient and
C3 distance. The existence theorem below derives this branch from original minimizers. -/
theorem endpointDistance_C3_of_branch (hF : F.IsSmoothStronglyConvex) (old : M)
    {Γ : (E × E) → ℝ → M} {e : OpenPartialHomeomorph (E × E) (E × E)}
    {W : Set (E × E)} {I : Set ℝ} {a b : ℝ}
    (hW : IsOpen W) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hEL : ∀ q ∈ W, F.IsEulerLagrangeOn (Γ (e.symm q)) I)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ (e.symm r.1))
        ⟨r.2, (1 : ℝ)⟩) (W ×ˢ I))
    (hmap : ∀ q ∈ W, MapsTo (Γ (e.symm q)) I (extChartAt 𝓘(ℝ, E) old).source)
    (hend : ∀ q ∈ W,
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) a) = q.1 ∧
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) b) = q.2)
    (hbranch : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ q ∈ W, (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal =
          (pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b).toReal) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    (∀ q ∈ W, HasFDerivAt d (F.endpointLengthDifferential old Γ e a b q) q) ∧
      ContDiffOn ℝ 2 (F.endpointLengthMomentum old Γ e a) W ∧
      ContDiffOn ℝ 2 (F.endpointLengthMomentum old Γ e b) W ∧ ContDiffOn ℝ 3 d W := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let d : E × E → ℝ := fun q ↦
    (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
      ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
  have hder (q : E × E) (hq : q ∈ W) :
      HasFDerivAt d (F.endpointLengthDifferential old Γ e a b q) q := by
    have hd := hF.hasFDerivAt_family_pathELength_endpoint old
      (Γ := fun q ↦ Γ (e.symm q)) hW hI hconn hG hq hab
      hsegment (hEL q hq) (hmap q hq)
    have ha : (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) a)) =ᶠ[𝓝 q]
        Prod.fst := Filter.Eventually.mono (hW.mem_nhds hq) (fun q hq ↦ (hend q hq).1)
    have hb : (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) b)) =ᶠ[𝓝 q]
        Prod.snd := Filter.Eventually.mono (hW.mem_nhds hq) (fun q hq ↦ (hend q hq).2)
    dsimp only at hd
    rw [ha.fderiv_eq, hb.fderiv_eq, fderiv_fst, fderiv_snd] at hd
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.mono (hW.mem_nhds hq) (fun q hq ↦ hbranch q hq))
  have hphase := hF.contDiffOn_chartPhase_of_tangentFamily_C2 old
    (Γ := fun q ↦ Γ (e.symm q)) (D := W ×ˢ I)
    (fun r hr ↦ hEL r.1 hr.1 r.2 hr.2) hG (fun r hr ↦ hmap r.1 hr.1 hr.2)
  have hm (t : ℝ) (ht : t ∈ I) :
      ContDiffOn ℝ 2 (F.endpointLengthMomentum old Γ e t) W := by
    intro q hq
    have hp := hphase.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun q hq ↦ show (q, t) ∈ W ×ˢ I from ⟨hq, ht⟩)
    have hz := (hF.chartTangent_of_isEulerLagrangeAt (hEL q hq t ht) old
      (hmap q hq ht)).2
    have hL := hF.contDiffOn_chartLength old |>.contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hz)
    exact ((contDiffAt_fiberLegendre hL).of_le (by simp)).comp_contDiffWithinAt q (hp q hq)
  have ha := hm a (hsegment (left_mem_Icc.mpr hab))
  have hb := hm b (hsegment (right_mem_Icc.mpr hab))
  refine ⟨hder, ha, hb, ?_⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 2) hW).2
  refine ⟨fun q hq ↦ (hder q hq).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have hg : ContDiffOn ℝ 2 (F.endpointLengthDifferential old Γ e a b) W :=
    (hb.clm_comp contDiffOn_const).sub (ha.clm_comp contDiffOn_const)
  exact hg.congr (fun q hq ↦ (hder q hq).fderiv)

variable [T2Space M] [PreconnectedSpace M]

/-- The original calibrated minimizing segment constructs a C3 distance branch and
its actual endpoint gradient, retaining the same complete family and endpoint inverse.
A common legal chart is required only on the compact central segment; its neighboring
parameter-time strip is derived, and no C3 family or distance identity is assumed. -/
theorem exists_calibrated_endpointDistanceC3 (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z₀ b) - u (Γ z₀ a) = dist (Γ z₀ a) (Γ z₀ b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z₀ a))
    (hx : ∀ t ∈ Icc a b, Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hinv : (fderiv ℝ (chartEndpointMap old Γ b) z₀).IsInvertible) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    let Q : E × E → M × M := fun q ↦
      ((extChartAt 𝓘(ℝ, E) old).symm q.1, (extChartAt 𝓘(ℝ, E) old).symm q.2)
    let d : E × E → ℝ := fun q ↦ (F.lengthEDist (Q q).1 (Q q).2).toReal
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E)) (W : Set (E × E)) (I : Set ℝ),
      (e : E × E → E × E) = chartEndpointMap old Γ b ∧
      z₀ ∈ e.source ∧ chartEndpointMap old Γ b z₀ ∈ W ∧
      e.source ⊆ chartEnergyDomain old ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      IsOpen W ∧ W ⊆ e.target ∧
      W ⊆ (extChartAt 𝓘(ℝ, E) old).target ×ˢ (extChartAt 𝓘(ℝ, E) old).target ∧
      IsOpen I ∧ IsPreconnected I ∧ Icc a b ⊆ I ∧
      (∀ q ∈ W, MapsTo (Γ (e.symm q)) I (extChartAt 𝓘(ℝ, E) old).source) ∧
      (∀ q ∈ W, Γ (e.symm q) a = (Q q).1 ∧ Γ (e.symm q) b = (Q q).2 ∧
        F.lengthEDist (Q q).1 (Q q).2 =
          pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b ∧
        d q = (F.chartLength old (e.symm q) : ℝ) * (b - a)) ∧
      (∀ t ∈ I, ContDiffOn ℝ 2 (endpointChartPhase old Γ e t) W) ∧
      (∀ q ∈ W, HasFDerivAt d (F.endpointLengthDifferential old Γ e a b q) q) ∧
      ContDiffOn ℝ 2 (F.endpointLengthMomentum old Γ e a) W ∧
      ContDiffOn ℝ 2 (F.endpointLengthMomentum old Γ e b) W ∧ ContDiffOn ℝ 3 d W := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨e, W, he, hze, hzW, hsub, hf, hi, hW, hWe, hWB, hbranch, _⟩ :=
    hF.exists_calibrated_endpointDistanceBranch hcomplete old old hab hEL hinit hG
      hz₀ hmin₀ hu hsat hdu (hx b (right_mem_Icc.mpr hab.le)) hinv
  have hGs : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ (e.symm r.1))
        ⟨r.2, (1 : ℝ)⟩) (e.target ×ˢ univ) := by
    have hpre : ContDiffOn ℝ 2 (fun r : (E × E) × ℝ ↦ (e.symm r.1, r.2))
        (e.target ×ˢ univ) :=
      (hi.comp contDiffOn_fst (fun _ hr ↦ hr.1)).prodMk contDiffOn_snd
    exact hG.comp hpre.contMDiffOn (fun r hr ↦ ⟨hsub (e.map_target hr.1), mem_univ _⟩)
  let O : Set ((E × E) × ℝ) := (e.target ×ˢ univ) ∩
    (fun r ↦ Γ (e.symm r.1) r.2) ⁻¹' (extChartAt 𝓘(ℝ, E) old).source
  have hO : IsOpen O := (contMDiffOn_positionFamily_of_tangentFamily
    (Γ := fun q ↦ Γ (e.symm q)) hGs).continuousOn
    |>.isOpen_inter_preimage (e.open_target.prod isOpen_univ) (isOpen_extChartAt_source old)
  have hcenter : e.symm (chartEndpointMap old Γ b z₀) = z₀ := by
    rw [← he]
    exact e.left_inv hze
  have htrace : {chartEndpointMap old Γ b z₀} ×ˢ Icc a b ⊆ O := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    have hq' : q = chartEndpointMap old Γ b z₀ := hq
    subst q
    refine ⟨⟨hWe hzW, mem_univ _⟩, ?_⟩
    change Γ (e.symm (chartEndpointMap old Γ b z₀)) t ∈
      (extChartAt 𝓘(ℝ, E) old).source
    rw [hcenter]
    exact hx t ht
  obtain ⟨U, V, hU, hV, hzU, hIV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hO htrace
  let I := connectedComponentIn V a
  have hI : IsOpen I := hV.connectedComponentIn
  have hseg : Icc a b ⊆ I :=
    isPreconnected_Icc.subset_connectedComponentIn (left_mem_Icc.mpr hab.le) hIV
  have hWI : ∀ q ∈ W ∩ U,
      MapsTo (Γ (e.symm q)) I (extChartAt 𝓘(ℝ, E) old).source := by
    intro q hq t ht
    exact (hUV (show (q, t) ∈ U ×ˢ V from
      ⟨hq.2, connectedComponentIn_subset V a ht⟩)).2
  have hG' := hGs.mono (show (W ∩ U) ×ˢ I ⊆ e.target ×ˢ univ from
    fun _ hr ↦ ⟨hWe hr.1.1, mem_univ _⟩)
  have hEL' : ∀ q ∈ W ∩ U, F.IsEulerLagrangeOn (Γ (e.symm q)) I :=
    fun q hq ↦ (hEL _ (hsub (e.map_target (hWe hq.1)))).mono (subset_univ _)
  have hend : ∀ q ∈ W ∩ U,
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) a) = q.1 ∧
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) b) = q.2 := by
    intro q hq
    rw [(hbranch q hq.1).1, (hbranch q hq.1).2.1]
    exact ⟨(extChartAt _ old).right_inv (hWB hq.1).1,
      (extChartAt _ old).right_inv (hWB hq.1).2⟩
  have hreg := hF.endpointDistance_C3_of_branch old (hW.inter hU) hI
    isPreconnected_connectedComponentIn hab.le hseg hEL' hG' hWI hend
    (fun q hq ↦ congrArg ENNReal.toReal (hbranch q hq.1).2.2.1)
  refine ⟨e, W ∩ U, I, he, hze, ⟨hzW, hzU (mem_singleton _)⟩, hsub, hf, hi,
    hW.inter hU, fun q hq ↦ hWe hq.1, fun q hq ↦ hWB hq.1, hI,
    isPreconnected_connectedComponentIn, hseg, hWI, fun q hq ↦ hbranch q hq.1,
    fun _ ht ↦ hF.contDiffOn_endpointChartPhase old hEL' hG' hWI ht, ?_⟩
  exact hreg

/-- A genuine affine calibration tube yields C3 original endpoint distance. Minimality,
calibration saturation, initial potential differentiability, and endpoint nonconjugacy
are all derived from the stated tube data. -/
theorem contDiffAt_endpointDistance_C3_of_affine_tube_data (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : ∀ t ∈ Icc a b, Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀) :
    ContDiffAt ℝ 3 (fun q : E × E ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal)
      (chartEndpointMap old Γ b z₀) := by
  obtain ⟨hdu, hmin, hsat, _⟩ := hF.affine_calibration_tube_data old hab
    (hEL z₀ hz₀) hu hx hU p hp hunit heq hspace hvelocity
  have hinv := hF.isInvertible_chartEndpointMap_of_calibrated_tube old hab hEL hinit hG
    hz₀ hx hU hsub p hp hunit
    (fun x hx v ↦ hF.chart_covector_le_chartLength old hu hU hsub p heq hx v)
    hspace hvelocity
  obtain ⟨e, W, I, _, _, hzW, _, _, _, hW, _, _, _, _, _, _, _, _, _, _, _, hC3⟩ :=
    hF.exists_calibrated_endpointDistanceC3 hcomplete old hab hEL hinit hG hz₀ hmin
      hu hsat hdu hx hinv
  exact hC3.contDiffAt (hW.mem_nhds hzW)

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
