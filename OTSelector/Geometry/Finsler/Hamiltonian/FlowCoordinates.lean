import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import OTSelector.Analysis.NormedSpace.CovectorSplitting
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.LocalC2

/-!
## Lemma skeleton

* **Conditions:** A joint C2 local phase flow, a C2 initial section over the kernel of a covector, affine initial base coordinates, positive flow box and nonzero pairing of the covector with central position velocity. The final inverse theorem requires completeness of E.
* **Objects:** The actual phase-flow position projection and a locally invertible C2 map from kernel-by-time parameters to position space, inside a prescribed open parameter neighborhood.
* **Proof detail:** Differentiate the initial flow identity in the spatial variable and the actual ODE in time. The joint derivative is the explicit covector splitting; transversality makes it invertible, so the inverse function theorem constructs the actual position chart and a smaller closed box.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
  https://www.jirka.org/ra/realanal2.pdf#page=51
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55.
  https://www.jirka.org/ra/realanal2.pdf#page=55
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38

**Relationship to the sources:** This adapts the transverse-plane flow-box argument to a position projection of phase flow. The normed-space completeness hypothesis and explicit local restrictions are accounted for; it does not identify the phase flow itself with a position-only ODE.
-/

/-!
# Position coordinates from an actual phase flow

A smooth initial section over the kernel of a covector and the time variable provide
local position coordinates. The initial derivative is derived from the flow's initial
identity and its actual ODE, then identified with the explicit covector splitting.
The inverse function theorem supplies the position chart on a neighborhood contained
in the original flow box, with joint C2 regularity of both coordinate maps.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Position projection of a phase flow launched from a covector-kernel section. -/
def hamiltonianFlowPositionMap {p : E →L[ℝ] ℝ}
    (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
    (ι : p.ker → E × (E →L[ℝ] ℝ)) (q : p.ker × ℝ) : E :=
  (Φ (ι q.1, q.2)).1

/-- The original positive flow box contains a neighborhood on which position composition is C2. -/
theorem contDiffAt_hamiltonianFlowPositionMap_initial
    {p : E →L[ℝ] ℝ}
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : p.ker → E × (E →L[ℝ] ℝ)} {q₀ : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ}
    (hC2 : ContDiffOn ℝ 2 Φ (closedBall q₀ r ×ˢ Icc (t₀ - T) (t₀ + T)))
    (hr : 0 < r) (hT : 0 < T) (hι : ContDiffAt ℝ 2 ι 0) (hι₀ : ι 0 = q₀) :
    ContDiffAt ℝ 2 (hamiltonianFlowPositionMap (p := p) Φ ι) (0, t₀) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hΦat : ContDiffAt ℝ 2 Φ (q₀, t₀) :=
    hC2.contDiffAt (prod_mem_nhds (closedBall_mem_nhds _ hrR)
      (Icc_mem_nhds (by linarith) (by linarith)))
  have hιfst : ContDiffAt ℝ 2 (fun q : p.ker × ℝ ↦ ι q.1) (0, t₀) :=
    hι.fst'
  rw [← hι₀] at hΦat
  have hcomp := hΦat.comp (0, t₀) (hιfst.prodMk contDiffAt_snd)
  exact hcomp.fst

/-- Actual spatial and time derivatives of the position flow give the covector splitting. -/
theorem hasFDerivAt_hamiltonianFlowPositionMap_initial
    {p : E →L[ℝ] ℝ} {X : E × (E →L[ℝ] ℝ) → E × (E →L[ℝ] ℝ)}
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : p.ker → E × (E →L[ℝ] ℝ)} {q₀ : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ X) t₀ q₀ r (t₀ - T) (t₀ + T) Φ)
    (hC2 : ContDiffOn ℝ 2 Φ (closedBall q₀ r ×ˢ Icc (t₀ - T) (t₀ + T)))
    (hr : 0 < r) (hT : 0 < T) (hι : ContDiffAt ℝ 2 ι 0) (hι₀ : ι 0 = q₀)
    (hbase : ∀ᶠ w in 𝓝 (0 : p.ker), (ι w).1 = q₀.1 + (w : E))
    (hv : p (X q₀).1 ≠ 0) :
    HasFDerivAt (hamiltonianFlowPositionMap (p := p) Φ ι)
      (covectorSplitting p (X q₀).1 hv).toContinuousLinearMap (0, t₀) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmem : ∀ᶠ w in 𝓝 (0 : p.ker), ι w ∈ closedBall q₀ r := by
    apply hι.continuousAt
    rw [hι₀]
    exact closedBall_mem_nhds _ hrR
  have hspace : HasFDerivAt (fun w ↦ hamiltonianFlowPositionMap (p := p) Φ ι (w, t₀))
      p.ker.subtypeL 0 := by
    apply (p.ker.subtypeL.hasFDerivAt.const_add q₀.1).congr_of_eventuallyEq
    filter_upwards [hmem, hbase] with w hw hb
    change (Φ (ι w, t₀)).1 = q₀.1 + (w : E)
    rw [hΦ.apply_initial (ι w) hw]
    exact hb
  have hq₀ : q₀ ∈ closedBall q₀ (r : ℝ) := mem_closedBall_self r.coe_nonneg
  have htime : HasDerivAt (fun t ↦ hamiltonianFlowPositionMap (p := p) Φ ι (0, t))
      (X q₀).1 t₀ := by
    have ht₀ : t₀ ∈ Icc (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
    have h := (hΦ.hasDerivWithinAt q₀ hq₀ t₀ ht₀).hasDerivAt
      (Icc_mem_nhds (by linarith) (by linarith))
    simpa [hamiltonianFlowPositionMap, hι₀, hΦ.apply_initial q₀ hq₀, Function.comp_def]
      using (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivAt t₀ h
  have hSmooth := contDiffAt_hamiltonianFlowPositionMap_initial (p := p) hC2 hr hT hι hι₀
  have hD : HasFDerivAt (hamiltonianFlowPositionMap (p := p) Φ ι)
      (fderiv ℝ (hamiltonianFlowPositionMap (p := p) Φ ι) (0, t₀)) (0, t₀) :=
    (hSmooth.differentiableAt (by norm_num)).hasFDerivAt
  have hleft := (HasFDerivAt.comp (f := fun w : p.ker ↦ (w, t₀))
    (g := hamiltonianFlowPositionMap (p := p) Φ ι) (0 : p.ker) hD
    (hasFDerivAt_prodMk_left (0 : p.ker) t₀)).unique hspace
  have hright := (HasFDerivAt.comp (f := fun t : ℝ ↦ ((0 : p.ker), t))
    (g := hamiltonianFlowPositionMap (p := p) Φ ι) t₀ hD
    (hasFDerivAt_prodMk_right (0 : p.ker) t₀)).unique htime.hasFDerivAt
  have heq : fderiv ℝ (hamiltonianFlowPositionMap (p := p) Φ ι) (0, t₀) =
      (covectorSplitting p (X q₀).1 hv).toContinuousLinearMap := by
    rw [covectorSplitting_toContinuousLinearMap]
    apply ContinuousLinearMap.prod_ext
    · simpa using hleft
    · rw [ContinuousLinearMap.coprod_comp_inr, hright]
      ext
      simp
  exact heq ▸ hD

/-- The actual projected flow gives C2 position coordinates within any prescribed open
parameter neighborhood, and its source contains a positive closed parameter-time box. -/
theorem exists_hamiltonianFlowCoordinates [CompleteSpace E]
    {p : E →L[ℝ] ℝ} {X : E × (E →L[ℝ] ℝ) → E × (E →L[ℝ] ℝ)}
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : p.ker → E × (E →L[ℝ] ℝ)} {q₀ : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ} {W : Set (p.ker × ℝ)}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ X) t₀ q₀ r (t₀ - T) (t₀ + T) Φ)
    (hC2 : ContDiffOn ℝ 2 Φ (closedBall q₀ r ×ˢ Icc (t₀ - T) (t₀ + T)))
    (hr : 0 < r) (hT : 0 < T) (hι : ContDiffAt ℝ 2 ι 0) (hι₀ : ι 0 = q₀)
    (hbase : ∀ᶠ w in 𝓝 (0 : p.ker), (ι w).1 = q₀.1 + (w : E))
    (hv : p (X q₀).1 ≠ 0) (hW : IsOpen W) (hW₀ : (0, t₀) ∈ W) :
    ∃ (e : OpenPartialHomeomorph (p.ker × ℝ) E) (ρ : ℝ≥0) (τ : ℝ),
      (e : p.ker × ℝ → E) = hamiltonianFlowPositionMap (p := p) Φ ι ∧
      (0, t₀) ∈ e.source ∧ q₀.1 ∈ e.target ∧
      e (0, t₀) = q₀.1 ∧ e.symm q₀.1 = (0, t₀) ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      e.source ⊆ W ∧
      MapsTo (fun q : p.ker × ℝ ↦ (ι q.1, q.2)) e.source
        (closedBall q₀ r ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
      0 < ρ ∧ 0 < τ ∧ τ ≤ T ∧
      closedBall (0 : p.ker) ρ ×ˢ Icc (t₀ - τ) (t₀ + τ) ⊆ e.source := by
  let ψ := hamiltonianFlowPositionMap (p := p) Φ ι
  have hSmooth : ContDiffAt ℝ 2 ψ (0, t₀) :=
    contDiffAt_hamiltonianFlowPositionMap_initial hC2 hr hT hι hι₀
  have hDeriv : HasFDerivAt ψ
      (covectorSplitting p (X q₀).1 hv).toContinuousLinearMap (0, t₀) :=
    hasFDerivAt_hamiltonianFlowPositionMap_initial hΦ hC2 hr hT hι hι₀ hbase hv
  have hψ₀ : ψ (0, t₀) = q₀.1 := by
    simp [ψ, hamiltonianFlowPositionMap, hι₀,
      hΦ.apply_initial q₀ (mem_closedBall_self r.coe_nonneg)]
  let e₀ := hSmooth.toOpenPartialHomeomorph ψ hDeriv (by norm_num)
  have he₀ : (0, t₀) ∈ e₀.source :=
    hSmooth.mem_toOpenPartialHomeomorph_source hDeriv (by norm_num)
  have hInv : ContDiffAt ℝ 2 e₀.symm (ψ (0, t₀)) :=
    hSmooth.to_localInverse hDeriv (by norm_num)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hιball : ∀ᶠ w in 𝓝 (0 : p.ker), ι w ∈ closedBall q₀ r := by
    apply hι.continuousAt
    rw [hι₀]
    exact closedBall_mem_nhds _ hrR
  let B : Set (p.ker × ℝ) := (ι ⁻¹' closedBall q₀ r) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hB : B ∈ 𝓝 ((0 : p.ker), t₀) :=
    prod_mem_nhds hιball (Ioo_mem_nhds (by linarith) (by linarith))
  let G : Set (p.ker × ℝ) := (W ∩ B) ∩
    ({q | ContDiffAt ℝ 2 ψ q} ∩ ψ ⁻¹' {x | ContDiffAt ℝ 2 e₀.symm x})
  have hG : G ∈ 𝓝 ((0 : p.ker), t₀) :=
    inter_mem (inter_mem (hW.mem_nhds hW₀) hB)
      (inter_mem (hSmooth.eventually (by norm_num))
        (hSmooth.continuousAt (hInv.eventually (by norm_num))))
  let e := e₀.restr G
  have he : (0, t₀) ∈ e.source := ⟨he₀, mem_interior_iff_mem_nhds.mpr hG⟩
  have hsource : e.source ⊆ G := fun _ hq ↦ interior_subset hq.2
  have heψ : (e : p.ker × ℝ → E) = ψ := rfl
  have hecenter : e (0, t₀) = q₀.1 := hψ₀
  have htarget : q₀.1 ∈ e.target := hecenter ▸ e.map_source he
  have hinvcenter : e.symm q₀.1 = (0, t₀) := by
    rw [← hecenter]
    exact e.left_inv he
  have hforward : ContDiffOn ℝ 2 e e.source := by
    intro q hq
    have hlocal : ContDiffAt ℝ 2 ψ q := (hsource hq).2.1
    exact hlocal.contDiffWithinAt
  have hinverse : ContDiffOn ℝ 2 e.symm e.target := by
    intro x hx
    have hg := (hsource (e.map_target hx)).2.2
    change ContDiffAt ℝ 2 e₀.symm (ψ (e.symm x)) at hg
    have hright : ψ (e.symm x) = x := e.right_inv hx
    rw [hright] at hg
    exact hg.contDiffWithinAt
  obtain ⟨ρ, τ, hρ, _, hτ, hτT, hbox⟩ :=
    LocalFlow.exists_pos_closed_flow_box_subset
      (r := 1) (T := T) (e.open_source.mem_nhds he) (by norm_num) hT
  exact ⟨e, ρ, τ, heψ, he, htarget, hecenter, hinvcenter, hforward, hinverse,
    fun _ hq ↦ (hsource hq).1.1, fun _ hq ↦ (hsource hq).1.2, hρ, hτ, hτT, hbox⟩

end OTSelector.Geometry
