import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.DistanceLocalizationNormalPath
import OTSelector.Geometry.Finsler.DistanceLocalizationPullbackLength
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationCompletePath.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationCompletePath`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationCompletePath

* **Conditions:** The prescribed complete actual Euler–Lagrange flow, compact unit initial states/time and a normal Lipschitz path of initial states.
* **Objects:** A uniform quadratic original-distance bound along the same diagonal flow path, with exact joint state/time tangent identities.
* **Proof detail:** Obtain joint smoothness by local ODE dependence, split its true diagonal velocity and apply the compact normal-path length estimate.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): Position-flow folds are allowed. The bound is constructed from the specified flow rather than an independent normal coordinate map.
-/

/-!
# Uniform distance bounds along the actual complete flow

Smoothness is produced from the prescribed complete Euler–Lagrange flow.
A compact set of unit initial states and a compact time interval supply one
quadratic upper constant for every normal Lipschitz path of initial states.
The position flow is allowed to fold.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The time column of the actual joint differential is the actual curve velocity. -/
theorem mfderiv_joint_time_column {f : V × ℝ → M} {z : V} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) f (z, t)) :
    mfderiv 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) f (z, t) (0, 1) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s ↦ f (z, s)) t 1 := by
  have hd := (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hi : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V × ℝ) (fun s ↦ (z, s)) t (1 : ℝ) =
      (0, (1 : ℝ)) := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  exact ((mfderiv_comp_apply (f := fun s ↦ (z, s)) (g := f) t hf
    hd.differentiableAt.mdifferentiableAt (1 : ℝ)).trans
      (congrArg (mfderiv 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) f (z, t)) hi)).symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The state column is the fixed-time derivative of the very same initial-state path. -/
theorem mfderiv_joint_state_column {f : V × ℝ → M} {z : ℝ → V} {s t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) f (z s, t))
    (hz : DifferentiableAt ℝ z s) :
    mfderiv 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) f (z s, t) (deriv z s, 0) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ f (z q, t)) s 1 := by
  have hd := hz.hasDerivAt.prodMk (hasDerivAt_const s t)
  have hi : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V × ℝ) (fun q ↦ (z q, t)) s (1 : ℝ) =
      (deriv z s, (0 : ℝ)) := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  exact ((mfderiv_comp_apply (f := fun q ↦ (z q, t)) (g := f) s hf
    hd.differentiableAt.mdifferentiableAt (1 : ℝ)).trans
      (congrArg (mfderiv 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) f (z s, t)) hi)).symm

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- A common compact set of actual unit initial states gives a uniform whole-time
quadratic distance estimate for every normal Lipschitz state path. Smooth flow
regularity and actual speed integrability are produced from the original flow. -/
theorem exists_uniform_complete_normal_path_upper
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {K : Set (E × E)} (hK : IsCompact K) (hKU : K ⊆ chartEnergyDomain old)
    (hunit : ∀ z ∈ K, (F.chartLength old z : ℝ) = 1) (lo hi : ℝ) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ {a b : ℝ}, a ≤ b → lo ≤ a → b ≤ hi →
      ∀ {z : ℝ → E × E} {L : ℝ≥0}, LipschitzOnWith L z (Icc a b) →
      MapsTo z (Icc a b) K → (L : ℝ) ≤ r →
      (∀ᵐ s ∂volume.restrict (Ioo a b),
        (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ, E) (Phi (z s) s) ↦
            (F.toFun ⟨Phi (z s) s, w⟩ : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi (z s)) s 1))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ Phi (z q) s) s 1) = 0) →
      (F.lengthEDist (Phi (z a) a) (Phi (z b) b)).toReal - (b - a) ≤
        (b - a) * (C : ℝ) * (L : ℝ) ^ 2 := by
  let f := fun q : (E × E) × ℝ ↦ Phi q.1 q.2
  have hf := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old
    (isOpen_chartEnergyDomain old) hEL (ι := fun z : E × E ↦ z)
    contDiffOn_id (mapsTo_id _) hinit).2
  have hU : IsOpen (chartEnergyDomain (E := E) old ×ˢ (univ : Set ℝ)) :=
    (isOpen_chartEnergyDomain old).prod isOpen_univ
  have hK' : IsCompact (K ×ˢ Icc lo hi) := hK.prod isCompact_Icc
  have hKU' : K ×ˢ Icc lo hi ⊆ chartEnergyDomain old ×ˢ univ :=
    fun q hq ↦ ⟨hKU hq.1, mem_univ _⟩
  have hdiff (q : (E × E) × ℝ) (hq : q.1 ∈ chartEnergyDomain old) :
      MDifferentiableAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) f q :=
    (hf.contMDiffAt (hU.mem_nhds ⟨hq, mem_univ _⟩)).mdifferentiableAt (by simp)
  have hu (q : (E × E) × ℝ) (hq : q ∈ K ×ˢ Icc lo hi) :
      F.mapVariationLength f ((0 : E × E), 1) (q, 0) = 1 := by
    change (F.toFun ⟨f q, mfderiv 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) f q
      (((0 : E × E), (1 : ℝ)) + (0 : (E × E) × ℝ))⟩ : ℝ) = 1
    rw [add_zero, mfderiv_joint_time_column (hdiff q (hKU hq.1))]
    change (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩) : ℝ) = 1
    rw [hF.speed_eq_of_isEulerLagrangeOn (hEL q.1 (hKU hq.1)) isPreconnected_univ
      (mem_univ q.2) (mem_univ 0), hinit q.1 (hKU hq.1)]
    exact hunit q.1 hq.1
  obtain ⟨r, hr, C, hb⟩ := hF.exists_uniform_normal_path_distance_upper
    hU hf hK' hKU' ((0 : E × E), 1) hu
  refine ⟨r, hr, C, ?_⟩
  intro a b hab hlo hhi z L hz hzK hL hnormal
  have hy : LipschitzOnWith (max L 1) (fun s ↦ (z s, s)) (Icc a b) :=
    hz.prodMk (LipschitzWith.id.lipschitzOnWith)
  apply hb hab hy (fun s hs ↦ ⟨hzK hs, ⟨hlo.trans hs.1, hs.2.trans hhi⟩⟩)
    L.coe_nonneg hL
  filter_upwards [hnormal,
    ae_restrict_of_ae (hz.ae_differentiableWithinAt_of_mem (μ := volume)),
    ae_restrict_mem measurableSet_Ioo] with s hs hd hsI
  have hscc := Ioo_subset_Icc_self hsI
  have hsn := Icc_mem_nhds hsI.1 hsI.2
  have hdz := (hd hscc).differentiableAt hsn
  have hder : deriv (fun q ↦ (z q, q)) s - ((0 : E × E), 1) =
      (deriv z s, (0 : ℝ)) := by
    have hh : deriv (fun q ↦ (z q, q)) s = (deriv z s, (1 : ℝ)) := by
      simpa only [id_eq] using (hdz.hasDerivAt.prodMk (hasDerivAt_id s)).deriv
    rw [hh]
    simp only [Prod.mk_sub_mk, sub_zero, sub_self]
  rw [hder]
  constructor
  · change max ‖deriv z s‖ ‖(0 : ℝ)‖ ≤ _
    rw [norm_zero, max_eq_left (norm_nonneg _)]
    exact norm_deriv_le_of_lipschitzOn hsn hz
  · rw [mfderiv_joint_time_column (hdiff (z s, s) (hKU (hzK hscc))),
      mfderiv_joint_state_column (hdiff (z s, s) (hKU (hzK hscc))) hdz]
    exact hs

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
