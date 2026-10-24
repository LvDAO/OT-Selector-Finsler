import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.ManifoldTubeCalibration
import OTSelector.Geometry.Finsler.MeasurableLegendre

/-!
# Geometry.Finsler.PotentialInitialState

* **Conditions:** An actual differentiable potential, its original nonzero energy covector and any legal chart at the same base point.
* **Objects:** Intrinsic initial tangent/covector identities, chart-independent phase validity and equality of complete curves built from different charts.
* **Proof detail:** Use chart chain-rule covariance and actual Legendre inverse identities, then identify intrinsic tangent vectors by energy injectivity.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Unit speed and calibrated partners are unnecessary for these intrinsic nonzero-covector identities.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialInitialState.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialInitialState`; the selected original proof blocks follow. -/
section

/-!
# Intrinsic initial states of actual potential-covector geodesics

The genuine chart Legendre inverse, applied to the actual coordinate differential of a potential,
recovers a nonzero original tangent whose energy covector is the intrinsic differential of that
same potential. The inverse tangent chart returns the original base point exactly. This identifies
initial states of the constructed complete covector family without a unit-speed or partner input.
Original fiber Legendre injectivity and Euler--Lagrange uniqueness then identify the complete
curves obtained from different legal charts at the same potential differentiability point.
Conversely, an intrinsic nonzero potential covector belongs to every legal chart momentum range,
so validity of the actual potential phase is itself intrinsic.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual chart inverse of a potential differential yields its intrinsic nonzero state. -/
theorem chartLegendreInverse_tangent_of_potentialDifferential
    (hF : F.IsSmoothStronglyConvex) (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source) {u : M → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hp : (extChartAt 𝓘(ℝ, E) old x,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x)) ∈
        F.chartLegendreRange old) :
    ∃ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 ∧
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
          ((hF.chartLegendreEquivRange old).symm
            ⟨(extChartAt 𝓘(ℝ, E) old x,
              fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
                (extChartAt 𝓘(ℝ, E) old x)), hp⟩) = ⟨x, v⟩ ∧
      fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  let _instPotentialStateFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _instPotentialStateFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  let e := extChartAt 𝓘(ℝ, E) old
  let p : F.chartLegendreRange old :=
    ⟨(e x, fderiv ℝ (u ∘ e.symm) (e x)), hp⟩
  let z := (hF.chartLegendreEquivRange old).symm p
  have hz := hF.chartLegendreEquivRange_symm_components old p
  let D : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) hx
  change A.toContinuousLinearMap = D at hA
  let v : TangentSpace 𝓘(ℝ, E) x := A.symm z.val.2
  have hDv : D v = z.val.2 := by
    rw [← hA]
    exact A.apply_symm_apply z.val.2
  have hzEq : z.val = (e x, D v) := Prod.ext hz.1 hDv.symm
  have hlegal : (e x, D v) ∈ chartEnergyDomain old := hzEq ▸ z.property
  have hv : v ≠ 0 := by
    intro hzero
    apply hz.2.2
    rw [← hDv, hzero, _root_.map_zero]
  refine ⟨v, hv, ?_, ?_⟩
  · change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z.val = ⟨x, v⟩
    rw [hzEq]
    exact tangentChart_symm_mfderiv_extChartAt old hx v
  · have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) := by
      simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
        mdifferentiableWithinAt_extChartAt_symm (e.map_source hx)
    have hdi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (e.symm (e x)) := by
      rwa [e.left_inv hx]
    have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)).comp D =
        ContinuousLinearMap.id ℝ _ := by
      simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
    have hchain : (fderiv ℝ (u ∘ e.symm) (e x)).comp D =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
      rw [← mfderiv_eq_fderiv, mfderiv_comp (e x) hdi hi,
        ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id, e.left_inv hx]
    have hm := hF.chartEnergy_fderiv_comp_mfderiv old hx v hlegal
    change (fiberLegendre (F.chartEnergy old) (e x, D v)).comp D =
      fderiv ℝ (F.fiberEnergy x) v at hm
    rw [← hzEq] at hm
    have hmomentum : fiberLegendre (F.chartEnergy old) z.val =
        fderiv ℝ (u ∘ e.symm) (e x) := hz.2.1
    rw [hmomentum] at hm
    exact hm.symm.trans hchain

/-- A curve with the actual inverse-phase initial tangent starts at the original point and
has the intrinsic energy covector of the original potential, with no prescribed speed. -/
theorem initialState_of_potential_covector_curve
    (hF : F.IsSmoothStronglyConvex) (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source) {u : M → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hp : (extChartAt 𝓘(ℝ, E) old x,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x)) ∈
        F.chartLegendreRange old)
    {c : ℝ → M}
    (hinit : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
          ((hF.chartLegendreEquivRange old).symm
            ⟨(extChartAt 𝓘(ℝ, E) old x,
              fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
                (extChartAt 𝓘(ℝ, E) old x)), hp⟩)) :
    c 0 = x ∧ ∃ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ = ⟨x, v⟩ ∧
      fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  obtain ⟨v, hv, hi, hpv⟩ :=
    hF.chartLegendreInverse_tangent_of_potentialDifferential old hx hd hp
  have ht := hinit.trans hi
  exact ⟨congrArg TotalSpace.proj ht, v, hv, ht, hpv⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Any nonzero original tangent with the actual potential covector places that potential's
coordinate differential in the actual Legendre range of every legal chart. -/
theorem mem_chartLegendreRange_of_intrinsic_potentialCovector
    (hF : F.IsSmoothStronglyConvex) (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source) {u : M → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (v : TangentSpace 𝓘(ℝ, E) x) (hv : v ≠ 0)
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    (extChartAt 𝓘(ℝ, E) old x,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x)) ∈
        F.chartLegendreRange old := by
  let _instPotentialForwardFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _instPotentialForwardFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  let e := extChartAt 𝓘(ℝ, E) old
  let D : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x
  have hD : Function.Bijective D := (isInvertible_mfderiv_extChartAt hx).bijective
  have hz : (e x, D v) ∈ chartEnergyDomain old :=
    ⟨e.map_source hx, fun hzero ↦ hv (hD.injective (hzero.trans D.map_zero.symm))⟩
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm (e.map_source hx)
  have hdi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (e.symm (e x)) := by
    rwa [e.left_inv hx]
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)).comp D =
      ContinuousLinearMap.id ℝ _ := by
    simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hchain : (fderiv ℝ (u ∘ e.symm) (e x)).comp D =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e x) hdi hi,
      ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id, e.left_inv hx]
  have hm := hF.chartEnergy_fderiv_comp_mfderiv old hx v hz
  have heq : fiberLegendre (F.chartEnergy old) (e x, D v) =
      fderiv ℝ (u ∘ e.symm) (e x) := by
    ext w
    obtain ⟨η, rfl⟩ := hD.surjective w
    exact congrArg (fun A ↦ A η) (hm.trans (hp.trans hchain.symm))
  refine ⟨⟨(e x, D v), hz⟩, ?_⟩
  change (e x, fiberLegendre (F.chartEnergy old) (e x, D v)) =
    (e x, fderiv ℝ (u ∘ e.symm) (e x))
  exact Prod.ext rfl heq

/-- Validity of the actual potential phase has a chart-independent intrinsic characterization. -/
theorem mem_chartLegendreRange_potential_iff_intrinsic
    (hF : F.IsSmoothStronglyConvex) (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source) {u : M → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    (extChartAt 𝓘(ℝ, E) old x,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x)) ∈
        F.chartLegendreRange old ↔
      ∃ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 ∧
        fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  constructor
  · intro hp
    obtain ⟨v, hv, _, hpv⟩ :=
      hF.chartLegendreInverse_tangent_of_potentialDifferential old hx hd hp
    exact ⟨v, hv, hpv⟩
  · rintro ⟨v, hv, hpv⟩
    exact hF.mem_chartLegendreRange_of_intrinsic_potentialCovector old hx hd v hv hpv

variable [T2Space M]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Equal actual initial energy covectors of nonzero tangents identify complete original curves. -/
theorem eq_of_complete_initial_fiberEnergy_covectors (hF : F.IsSmoothStronglyConvex)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hd : F.IsEulerLagrangeOn d univ) (x : M)
    {v w : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0) (hw : w ≠ 0)
    (hci : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ = ⟨x, v⟩)
    (hdi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ = ⟨x, w⟩)
    (hp : fderiv ℝ (F.fiberEnergy x) v = fderiv ℝ (F.fiberEnergy x) w) : c = d := by
  let _instPotentialStateUniqueFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _instPotentialStateUniqueFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hvw : v = w := hF.injOn_fiberEnergy_legendre x hv hw hp
  have ht : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ := by
    rw [hci, hdi, hvw]
  funext t
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hd
    (mem_univ 0) ht (mem_univ t)

/-- Two genuine chart constructions from the same differentiable potential produce the same
complete original curve on overlaps, without a unit-speed or common-branch assumption. -/
theorem eq_of_complete_potential_covector_charts
    (hF : F.IsSmoothStronglyConvex) (old new : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hx' : x ∈ (extChartAt 𝓘(ℝ, E) new).source) {u : M → ℝ}
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hp : (extChartAt 𝓘(ℝ, E) old x,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x)) ∈
        F.chartLegendreRange old)
    (hq : (extChartAt 𝓘(ℝ, E) new x,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) new).symm) (extChartAt 𝓘(ℝ, E) new x)) ∈
        F.chartLegendreRange new)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hd : F.IsEulerLagrangeOn d univ)
    (hci : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
          ((hF.chartLegendreEquivRange old).symm
            ⟨(extChartAt 𝓘(ℝ, E) old x,
              fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
                (extChartAt 𝓘(ℝ, E) old x)), hp⟩))
    (hdi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨new, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
          ((hF.chartLegendreEquivRange new).symm
            ⟨(extChartAt 𝓘(ℝ, E) new x,
              fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) new).symm)
                (extChartAt 𝓘(ℝ, E) new x)), hq⟩)) : c = d := by
  obtain ⟨_, v, hv, hcv, hpv⟩ :=
    hF.initialState_of_potential_covector_curve old hx hdu hp hci
  obtain ⟨_, w, hw, hdw, hpw⟩ :=
    hF.initialState_of_potential_covector_curve new hx' hdu hq hdi
  exact hF.eq_of_complete_initial_fiberEnergy_covectors hc hd x hv hw hcv hdw
    (hpv.trans hpw.symm)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
