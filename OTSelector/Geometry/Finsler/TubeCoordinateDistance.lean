import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.EndpointDistanceBranch
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TubeCoordinateFirstVariation

/-!
# Geometry.Finsler.TubeCoordinateDistance

* **Conditions:** A genuine smooth tube map and an actual complete endpoint branch with invertible endpoint differential.
* **Objects:** Original distance expressed smoothly in actual tube coordinates with its true intrinsic first differential.
* **Proof detail:** Upgrade the existing endpoint inverse using smooth original flow, keep separate charts at the two endpoints and compose with the actual tube maps.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): Nonconjugacy remains explicit here; later tube-kernel lemmas derive it. The genuine tube is never identified with an old chart.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateDistance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateDistance`; the selected original proof blocks follow. -/
section

/-!
# Original distance in genuine smooth tube coordinates

The actual two-endpoint branch already identifies global distance with original
initial speed times elapsed time. Smoothness of that same complete family upgrades
its actual endpoint inverse, using charts only at the two endpoints. Composing
with a genuine smooth tube map gives the original distance and its actual first
jet in the new coordinates; the tube map is never declared to be an old chart.
The true two-endpoint differential's invertibility remains an explicit internal
nonconjugacy input. Its derivation from a regular calibrated tube, and the new
coordinates' second-order compliance formula, are separate unresolved steps.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original Finsler length distance evaluated at two points of the actual tube. -/
def tubeCoordinateDistance (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph (ℝ × W) M) (q : (ℝ × W) × (ℝ × W)) : ℝ :=
  (F.lengthEDist (Y q.1) (Y q.2)).toReal

/-- Genuine endpoint coordinate changes from the actual tube to two independent charts. -/
def tubeEndpointChart (initial terminal : M) (Y : OpenPartialHomeomorph (ℝ × W) M)
    (q : (ℝ × W) × (ℝ × W)) : E × E :=
  (extChartAt 𝓘(ℝ, E) initial (Y q.1), extChartAt 𝓘(ℝ, E) terminal (Y q.2))

namespace IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The original globally minimizing branch has a smooth distance and its actual
intrinsic endpoint-momentum first jet in independent endpoint charts. Smoothness of the given
complete family is derived from its exact initial tangent identity. -/
theorem endpointDistance_smooth_of_nonconjugate (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial terminal : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain initial)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z₀ b) - u (Γ z₀ a) = dist (Γ z₀ a) (Γ z₀ b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z₀ a))
    (hx : Γ z₀ b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hinv : (fderiv ℝ (chartEndpointMap terminal Γ b) z₀).IsInvertible) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) initial).symm q.1)
        ((extChartAt 𝓘(ℝ, E) terminal).symm q.2)).toReal
    let q₀ := chartEndpointMap terminal Γ b z₀
    let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ z₀ t) →L[ℝ] ℝ := fun t ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ z₀ t) ↦
        (F.toFun ⟨Γ z₀ t, v⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z₀) t 1)
    ContDiffAt ℝ ∞ d q₀ ∧
      d q₀ = (F.chartLength initial z₀ : ℝ) * (b - a) ∧
      HasFDerivAt d
        ((p b).comp (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
          (fun q ↦ (extChartAt 𝓘(ℝ, E) terminal).symm q.2) q₀) -
        (p a).comp (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
          (fun q ↦ (extChartAt 𝓘(ℝ, E) initial).symm q.1) q₀)) q₀ := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hG := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth initial
    (isOpen_chartEnergyDomain initial) hEL contDiffOn_id (fun _ hz ↦ hz) hinit).1
  have hG₂ := hG.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hposition : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun q ↦ Γ q.1 q.2) (chartEnergyDomain initial ×ˢ univ) :=
    fun q hq ↦ (Bundle.contMDiffWithinAt_totalSpace.mp (hG q hq)).1
  have hp := hposition.contMDiffAt
    (((isOpen_chartEnergyDomain initial).prod isOpen_univ).mem_nhds
      (show (z₀, b) ∈ chartEnergyDomain initial ×ˢ univ from ⟨hz₀, mem_univ _⟩))
  have hs := hp.comp z₀ ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) terminal)
      (Γ z₀ b) := contMDiffAt_extChartAt'
        (by simpa only [extChartAt_source] using hx)
  have hP : ContDiffAt ℝ ∞ (chartEndpointMap terminal Γ b) z₀ :=
    contDiffAt_fst.prodMk (hc.comp z₀ hs).contDiffAt
  obtain ⟨e, U, he, hze, hzU, hsub, _, hi₂, hU, hUe, _, hbranch, _⟩ :=
    hF.exists_calibrated_endpointDistanceBranch hcomplete initial terminal hab hEL hinit hG₂
      hz₀ hmin₀ hu hsat hdu hx hinv
  let q₀ := chartEndpointMap terminal Γ b z₀
  have hcenter : e.symm q₀ = z₀ := by
    dsimp only [q₀]
    rw [← he]
    exact e.left_inv hze
  obtain ⟨A, hA⟩ := hinv
  have hde : HasFDerivAt e A.toContinuousLinearMap (e.symm q₀) := by
    rw [hcenter, he, hA]
    exact (hP.differentiableAt (by simp)).hasFDerivAt
  have hei : ContDiffAt ℝ ∞ e.symm q₀ :=
    e.contDiffAt_symm (hUe hzU) hde (by simpa only [hcenter, he] using hP)
  have hL := (hF.contDiffOn_chartLength initial).contDiffAt
    ((isOpen_chartEnergyDomain initial).mem_nhds hz₀)
  have hL' : ContDiffAt ℝ ∞ (fun z ↦ (F.chartLength initial z : ℝ)) (e.symm q₀) := by
    simpa only [hcenter] using hL
  have heq : (fun q : E × E ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) initial).symm q.1)
        ((extChartAt 𝓘(ℝ, E) terminal).symm q.2)).toReal) =ᶠ[𝓝 q₀]
      (fun q ↦ (b - a) * (F.chartLength initial (e.symm q) : ℝ)) := by
    filter_upwards [hU.mem_nhds hzU] with q hq
    exact (hbranch q hq).2.2.2.trans (mul_comm _ _)
  have hpre : ContDiffOn ℝ 2 (fun r : (E × E) × ℝ ↦ (e.symm r.1, r.2))
      (U ×ˢ univ) :=
    ((hi₂.mono hUe).comp contDiffOn_fst (fun _ hr ↦ hr.1)).prodMk contDiffOn_snd
  have hGs : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ (e.symm r.1))
        ⟨r.2, (1 : ℝ)⟩) (U ×ˢ univ) :=
    hG₂.comp hpre.contMDiffOn
      (fun r hr ↦ ⟨hsub (e.map_target (hUe hr.1)), mem_univ _⟩)
  have hd := hF.hasFDerivAt_family_pathELength_mfderiv_across_charts
    (Γ := fun q ↦ Γ (e.symm q)) hU isOpen_univ
    hGs hzU hab.le (subset_univ _) (hEL _ (hsub (e.map_target (hUe hzU))))
  have ha : (fun q ↦ Γ (e.symm q) a) =ᶠ[𝓝 q₀]
      (fun q ↦ (extChartAt 𝓘(ℝ, E) initial).symm q.1) := by
    filter_upwards [hU.mem_nhds hzU] with q hq
    exact (hbranch q hq).1
  have hb : (fun q ↦ Γ (e.symm q) b) =ᶠ[𝓝 q₀]
      (fun q ↦ (extChartAt 𝓘(ℝ, E) terminal).symm q.2) := by
    filter_upwards [hU.mem_nhds hzU] with q hq
    exact (hbranch q hq).2.1
  dsimp only at hd
  rw [ha.mfderiv_eq, hb.mfderiv_eq] at hd
  have hdist : (fun q : E × E ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) initial).symm q.1)
        ((extChartAt 𝓘(ℝ, E) terminal).symm q.2)).toReal) =ᶠ[𝓝 q₀]
      (fun q ↦ (pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b).toReal) := by
    filter_upwards [hU.mem_nhds hzU] with q hq
    exact congrArg ENNReal.toReal (hbranch q hq).2.2.1
  refine ⟨((contDiffAt_const.mul (hL'.comp q₀ hei)).congr_of_eventuallyEq heq), ?_, ?_⟩
  · simpa only [hcenter] using (hbranch q₀ hzU).2.2.2
  · have hc : e.symm (chartEndpointMap terminal Γ b z₀) = z₀ := hcenter
    rw [hc] at hd
    simpa only [q₀] using hd.congr_of_eventuallyEq hdist

/-- The original distance in an actual smooth tube has the same smooth minimizing
branch, composed with genuine endpoint coordinate changes. Only endpoint charts and
actual endpoint nonconjugacy are supplied; no affine old-chart calibration is used. -/
theorem tubeCoordinateDistance_smooth_of_nonconjugate (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial terminal : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain initial)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z₀ b) - u (Γ z₀ a) = dist (Γ z₀ a) (Γ z₀ b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z₀ a))
    (hx : Γ z₀ b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hinv : (fderiv ℝ (chartEndpointMap terminal Γ b) z₀).IsInvertible)
    (Y : OpenPartialHomeomorph (ℝ × W) M)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    {qa qb : ℝ × W} (haY : qa ∈ Y.source) (hbY : qb ∈ Y.source)
    (hea : Y qa = Γ z₀ a) (heb : Y qb = Γ z₀ b) :
    let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ z₀ t) →L[ℝ] ℝ := fun t ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ z₀ t) ↦
        (F.toFun ⟨Γ z₀ t, v⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z₀) t 1)
    ContDiffAt ℝ ∞ (F.tubeCoordinateDistance Y) (qa, qb) ∧
      F.tubeCoordinateDistance Y (qa, qb) = (F.chartLength initial z₀ : ℝ) * (b - a) ∧
      HasFDerivAt (F.tubeCoordinateDistance Y)
        ((p b).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.2) (qa, qb)) -
        (p a).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.1) (qa, qb))) (qa, qb) := by
  have hstart : Γ z₀ a = (extChartAt 𝓘(ℝ, E) initial).symm z₀.1 := by
    have h := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) (hinit z₀ hz₀)
    rw [tangentChart_symm_eq initial hz₀.1 z₀.2] at h
    exact h
  have hxa : Y qa ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hea, hstart]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target hz₀.1
  have hxb : Y qb ∈ (extChartAt 𝓘(ℝ, E) terminal).source := heb.symm ▸ hx
  have hya := hY.contMDiffAt (Y.open_source.mem_nhds haY)
  have hyb := hY.contMDiffAt (Y.open_source.mem_nhds hbY)
  have hca : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) initial)
      (Y qa) := contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hxa)
  have hcb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) terminal)
      (Y qb) := contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hxb)
  have hcoord : ContDiffAt ℝ ∞ (tubeEndpointChart initial terminal Y) (qa, qb) :=
    (((hca.comp qa hya).contDiffAt).comp (qa, qb) contDiffAt_fst).prodMk
      (((hcb.comp qb hyb).contDiffAt).comp (qa, qb) contDiffAt_snd)
  have hq : tubeEndpointChart initial terminal Y (qa, qb) =
      chartEndpointMap terminal Γ b z₀ := by
    apply Prod.ext
    · change extChartAt 𝓘(ℝ, E) initial (Y qa) = z₀.1
      rw [hea, hstart, (extChartAt 𝓘(ℝ, E) initial).right_inv hz₀.1]
    · exact congrArg (extChartAt 𝓘(ℝ, E) terminal) heb
  let d : E × E → ℝ := fun q ↦
    (F.lengthEDist ((extChartAt 𝓘(ℝ, E) initial).symm q.1)
      ((extChartAt 𝓘(ℝ, E) terminal).symm q.2)).toReal
  have heq : F.tubeCoordinateDistance Y =ᶠ[𝓝 (qa, qb)]
      d ∘ tubeEndpointChart initial terminal Y := by
    have hna : ∀ᶠ q : (ℝ × W) × (ℝ × W) in 𝓝 (qa, qb),
        Y q.1 ∈ (extChartAt 𝓘(ℝ, E) initial).source :=
      (hya.continuousAt.comp continuousAt_fst).preimage_mem_nhds
      ((isOpen_extChartAt_source initial).mem_nhds hxa)
    have hnb : ∀ᶠ q : (ℝ × W) × (ℝ × W) in 𝓝 (qa, qb),
        Y q.2 ∈ (extChartAt 𝓘(ℝ, E) terminal).source :=
      (hyb.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      ((isOpen_extChartAt_source terminal).mem_nhds hxb)
    filter_upwards [hna, hnb] with q hqa hqb
    dsimp only [tubeCoordinateDistance, tubeEndpointChart, Function.comp_def, d]
    rw [(extChartAt 𝓘(ℝ, E) initial).left_inv hqa,
      (extChartAt 𝓘(ℝ, E) terminal).left_inv hqb]
  obtain ⟨hsm, hval, hd⟩ := hF.endpointDistance_smooth_of_nonconjugate hcomplete
    initial terminal hab hEL hinit hz₀ hmin₀ hu hsat hdu hx hinv
  change ContDiffAt ℝ ∞ d _ at hsm
  change HasFDerivAt d _ _ at hd
  rw [← hq] at hsm hd
  have hder := hd.comp (qa, qb) ((hcoord.differentiableAt (by simp)).hasFDerivAt)
  have hca' : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (fun q ↦ (extChartAt 𝓘(ℝ, E) initial).symm q.1)
      (tubeEndpointChart initial terminal Y (qa, qb)) := by
    exact (((contMDiffOn_extChartAt_symm (n := ∞) initial).contMDiffAt
      ((isOpen_extChartAt_target initial).mem_nhds
        ((extChartAt 𝓘(ℝ, E) initial).map_source hxa))).comp
      (tubeEndpointChart initial terminal Y (qa, qb))
      (contDiffAt_fst (𝕜 := ℝ) (n := ∞)).contMDiffAt).mdifferentiableAt (by simp)
  have hcb' : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (fun q ↦ (extChartAt 𝓘(ℝ, E) terminal).symm q.2)
      (tubeEndpointChart initial terminal Y (qa, qb)) := by
    exact (((contMDiffOn_extChartAt_symm (n := ∞) terminal).contMDiffAt
      ((isOpen_extChartAt_target terminal).mem_nhds
        ((extChartAt 𝓘(ℝ, E) terminal).map_source hxb))).comp
      (tubeEndpointChart initial terminal Y (qa, qb))
      (contDiffAt_snd (𝕜 := ℝ) (n := ∞)).contMDiffAt).mdifferentiableAt (by simp)
  have hyae : ((fun q : E × E ↦ (extChartAt 𝓘(ℝ, E) initial).symm q.1) ∘
      tubeEndpointChart initial terminal Y) =ᶠ[𝓝 (qa, qb)] (fun q ↦ Y q.1) := by
    have hn : ∀ᶠ q : (ℝ × W) × (ℝ × W) in 𝓝 (qa, qb),
        Y q.1 ∈ (extChartAt 𝓘(ℝ, E) initial).source :=
      (hya.continuousAt.comp continuousAt_fst).preimage_mem_nhds
        ((isOpen_extChartAt_source initial).mem_nhds hxa)
    filter_upwards [hn] with q hq
    exact (extChartAt 𝓘(ℝ, E) initial).left_inv hq
  have hybe : ((fun q : E × E ↦ (extChartAt 𝓘(ℝ, E) terminal).symm q.2) ∘
      tubeEndpointChart initial terminal Y) =ᶠ[𝓝 (qa, qb)] (fun q ↦ Y q.2) := by
    have hn : ∀ᶠ q : (ℝ × W) × (ℝ × W) in 𝓝 (qa, qb),
        Y q.2 ∈ (extChartAt 𝓘(ℝ, E) terminal).source :=
      (hyb.continuousAt.comp continuousAt_snd).preimage_mem_nhds
        ((isOpen_extChartAt_source terminal).mem_nhds hxb)
    filter_upwards [hn] with q hq
    exact (extChartAt 𝓘(ℝ, E) terminal).left_inv hq
  have hcha := (mfderiv_comp (qa, qb) hca'
    (hcoord.contMDiffAt.mdifferentiableAt (by simp))).symm.trans hyae.mfderiv_eq
  have hchb := (mfderiv_comp (qa, qb) hcb'
    (hcoord.contMDiffAt.mdifferentiableAt (by simp))).symm.trans hybe.mfderiv_eq
  rw [mfderiv_eq_fderiv] at hcha hchb
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, hcha, hchb] at hder
  refine ⟨(hsm.comp (qa, qb) hcoord).congr_of_eventuallyEq heq, ?_,
    hder.congr_of_eventuallyEq heq⟩
  have hv := heq.eq_of_nhds
  rw [Function.comp_apply, hq] at hv
  exact hv.trans hval

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
