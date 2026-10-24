import OTSelector.Analysis.Calculus.Variational.EulerLagrangeReparam
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeLocality
import OTSelector.Geometry.Finsler.TubeCoordinateEnergy

/-!
# Geometry.Finsler.TubeCoordinateEulerLagrange

* **Conditions:** An intrinsic original Euler–Lagrange germ lying in a genuine smooth tube.
* **Objects:** The actual Euler–Lagrange momentum equation for the literal tube energy along the actual inverse-coordinate curve.
* **Proof detail:** Identify tube energy locally with the actual old-chart pullback and transfer the intrinsic equation by covariance, choosing charts only near each time.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateEulerLagrange.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateEulerLagrange`; the selected original proof blocks follow. -/
section

/-!
# Actual Euler--Lagrange equations in smooth tube coordinates

The original tangent energy agrees locally with the ordinary pullback of every
valid old-chart energy. The intrinsic equation therefore gives the actual momentum
equation of the literal tube energy for the actual inverse-coordinate curve.
The old chart is chosen only near each time by the intrinsic equation itself.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The literal tube energy equals the actual chart pullback wherever both coordinates hold. -/
theorem tubeCoordinateEnergy_eq_chartPullback (F : ContinuousFinslerNorm E M)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (old : M) {z : V × V} (hz : z.1 ∈ Y.source)
    (hx : Y z.1 ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    F.tubeCoordinateEnergy Y z =
      pullbackEnergy (extChartAt 𝓘(ℝ, E) old ∘ Y) (F.chartEnergy old) z := by
  have hdY := (hY.contMDiffAt (Y.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hχ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) old)
      (extChartAt 𝓘(ℝ, E) old).source := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := old) (n := ∞))
  have hdχ := (hχ.contMDiffAt
    ((isOpen_extChartAt_source old).mem_nhds hx)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z.1 hdχ hdY
  rw [mfderiv_eq_fderiv] at hd
  rw [pullbackEnergy, tangentLift, hd, F.chartEnergy_eq_chartLength_sq]
  change F.tubeCoordinateEnergy Y z =
    (F.chartLength old (extChartAt 𝓘(ℝ, E) old (Y z.1),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Y z.1)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y z.1 z.2)) : ℝ) ^ 2 / 2
  rw [F.chartLength_mfderiv_extChartAt old hx]
  rfl

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- Intrinsic Euler--Lagrange curves satisfy the literal tube equation on a genuine
open time neighborhood. Both the coordinate curve and its nonzero velocity are actual. -/
theorem exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt
    (hF : F.IsSmoothStronglyConvex) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hYi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (htY : c t ∈ Y.target) :
    ∃ I : Set ℝ, IsOpen I ∧ t ∈ I ∧ MapsTo c I Y.target ∧
      ContDiffOn ℝ 2 (Y.symm ∘ c) I ∧
      (∀ s ∈ I, deriv (Y.symm ∘ c) s ≠ 0) ∧
      ∀ s ∈ I, HasDerivAt
        (fun r ↦ fiberLegendre (F.tubeCoordinateEnergy Y)
          ((Y.symm ∘ c) r, deriv (Y.symm ∘ c) r))
        (baseEnergyDifferential (F.tubeCoordinateEnergy Y)
          ((Y.symm ∘ c) s, deriv (Y.symm ∘ c) s)) s := by
  obtain ⟨old, J, hJ, htJ, hcmap, hx, hxphase, hxEL⟩ := hc
  have hcC2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 c J := by
    have h := ((contMDiffOn_extChartAt_symm old).of_le (by norm_num : 2 ≤ ∞)).comp
      hx.contMDiffOn (fun s hs ↦ (hxphase s hs).1)
    refine h.congr fun s hs ↦ ?_
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hcmap hs)).symm
  let I := J ∩ c ⁻¹' Y.target
  have hI : IsOpen I := hcC2.continuousOn.isOpen_inter_preimage hJ Y.open_target
  have htI : t ∈ I := ⟨htJ, htY⟩
  have hcY : MapsTo c I Y.target := fun _ hs ↦ hs.2
  let y := Y.symm ∘ c
  let φ := extChartAt 𝓘(ℝ, E) old ∘ Y
  let U := Y.source ∩ Y ⁻¹' (extChartAt 𝓘(ℝ, E) old).source
  have hU : IsOpen U := Y.continuousOn.isOpen_inter_preimage Y.open_source
    (isOpen_extChartAt_source old)
  have hy : ContDiffOn ℝ 2 y I :=
    (((hYi.of_le (by norm_num : 2 ≤ ∞)).comp (hcC2.mono inter_subset_left)
      hcY)).contDiffOn
  have hyU : MapsTo y I U := by
    intro s hs
    refine ⟨Y.map_target hs.2, ?_⟩
    change Y (Y.symm (c s)) ∈ (extChartAt 𝓘(ℝ, E) old).source
    rw [Y.right_inv hs.2]
    exact hcmap hs.1
  have hχ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) old)
      (extChartAt 𝓘(ℝ, E) old).source := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := old) (n := ∞))
  have hφ : ContDiffOn ℝ 2 φ U :=
    ((hχ.of_le (by norm_num : 2 ≤ ∞)).comp
      ((hY.of_le (by norm_num : 2 ≤ ∞)).mono inter_subset_left)
      (fun _ hq ↦ hq.2)).contDiffOn
  have heq : EqOn (φ ∘ y) (extChartAt 𝓘(ℝ, E) old ∘ c) I := by
    intro s hs
    change extChartAt 𝓘(ℝ, E) old (Y (Y.symm (c s))) = _
    rw [Y.right_inv hs.2]
    rfl
  have hlift (s : ℝ) (hs : s ∈ I) :
      tangentLift φ (y s, deriv y s) =
        ((extChartAt 𝓘(ℝ, E) old ∘ c) s,
          deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s) := by
    rw [tangentLift_curve_eq
      ((hφ.contDiffAt (hU.mem_nhds (hyU hs))).differentiableAt (by norm_num))
      ((hy.contDiffAt (hI.mem_nhds hs)).differentiableAt (by norm_num)),
      heq hs, heq.deriv hI hs]
  have hphase : ∀ s ∈ I, tangentLift φ (y s, deriv y s) ∈ chartEnergyDomain old := by
    intro s hs
    rw [hlift s hs]
    exact hxphase s hs.1
  have hyEL : ∀ s ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (pullbackEnergy φ (F.chartEnergy old)) (y r, deriv y r))
      (baseEnergyDifferential (pullbackEnergy φ (F.chartEnergy old))
        (y s, deriv y s)) s := by
    intro s hs
    apply hasDerivAt_eulerLagrange_pullback hU (isOpen_chartEnergyDomain old)
      hφ ((hF.contDiffOn_chartEnergy old).of_le (by norm_num : 2 ≤ ∞))
      hI hy hyU hphase hs
    exact hasDerivAt_eulerLagrange_congr
      (heq.symm.eventuallyEq_of_mem (hI.mem_nhds hs)) (hxEL s hs.1)
  have henergy : EqOn (F.tubeCoordinateEnergy Y)
      (pullbackEnergy φ (F.chartEnergy old)) (U ×ˢ (univ : Set V)) := by
    intro z hz
    exact F.tubeCoordinateEnergy_eq_chartPullback hY old hz.1.1 hz.1.2
  refine ⟨I, hI, htI, hcY, hy, ?_, ?_⟩
  · intro s hs hv
    have hn := (hphase s hs).2
    change fderiv ℝ φ (y s) (deriv y s) ≠ 0 at hn
    exact hn (by rw [hv, _root_.map_zero])
  · exact (eulerLagrange_congr_of_eqOn (hU.prod isOpen_univ) hI henergy
      (fun s hs ↦ ⟨hyU hs, mem_univ _⟩)).mpr hyEL

/-- The actual inverse-coordinate curve obeys the literal tube energy equation at the time. -/
theorem hasDerivAt_tubeCoordinateEulerLagrange_of_isEulerLagrangeAt
    (hF : F.IsSmoothStronglyConvex) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hYi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (htY : c t ∈ Y.target) :
    HasDerivAt
      (fun r ↦ fiberLegendre (F.tubeCoordinateEnergy Y)
        ((Y.symm ∘ c) r, deriv (Y.symm ∘ c) r))
      (baseEnergyDifferential (F.tubeCoordinateEnergy Y)
        ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t)) t := by
  obtain ⟨I, _, ht, _, _, _, hEL⟩ :=
    hF.exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt hY hYi hc htY
  exact hEL t ht

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
