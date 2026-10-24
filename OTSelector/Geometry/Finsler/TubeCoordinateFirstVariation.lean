import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.FamilyFrechetFirstVariation
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.TubeCoordinateFirstVariation

* **Conditions:** A jointly regular actual intrinsic family with nonzero central tangents on a compact time segment spanning potentially multiple legal charts.
* **Objects:** One intrinsic Frechet path-length endpoint first-variation formula across all those charts.
* **Proof detail:** Subdivide the segment into finitely many legal chart intervals, differentiate their genuine length integrals and cancel intrinsic momentum terms at internal endpoints.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateFirstVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateFirstVariation`; the selected original proof blocks follow. -/
section

/-!
# Intrinsic first variation across finitely many legal charts

The compact central segment is subdivided into legal chart intervals. Original path
length is converted to its actual speed integral, and the intrinsic endpoint momentum
terms cancel at each interior subdivision point. No single chart, prescribed subdivision,
or coordinate variation is assumed for the entire segment.
-/

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- The true first variation of original path length has only the two intrinsic endpoint
momenta, even when the central path requires different charts at different times. -/
theorem hasFDerivAt_family_pathELength_mfderiv_across_charts
    (hF : F.IsSmoothStronglyConvex) {Γ : W → ℝ → M}
    {B : Set W} {I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ I))
    {s₀ : W} {a b : ℝ} (hs₀ : s₀ ∈ B) (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hEL : F.IsEulerLagrangeOn (Γ s₀) I) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ s₀ t) →L[ℝ] ℝ := fun t ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ s₀ t) ↦ (F.toFun ⟨Γ s₀ t, v⟩ : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1)
    HasFDerivAt (fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s) a b).toReal)
      ((p b).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s b) s₀) -
        (p a).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s a) s₀)) s₀ := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ s₀ t) →L[ℝ] ℝ := fun t ↦
    fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ s₀ t) ↦ (F.toFun ⟨Γ s₀ t, v⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1)
  let D : ℝ → W →L[ℝ] ℝ := fun t ↦
    (p t).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s t) s₀)
  let speed : W → ℝ → ℝ := fun s t ↦
    (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s) ⟨t, (1 : ℝ)⟩) : ℝ)
  have hspeed {s : W} (hs : s ∈ B) : ContinuousOn (speed s) I := by
    apply NNReal.continuous_coe.comp_continuousOn
    apply F.continuous_toFun.comp_continuousOn
    exact hG.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hs, ht⟩)
  have hint {s : W} (hs : s ∈ B) {c d : ℝ} (hcd : c ≤ d)
      (hcdI : Icc c d ⊆ I) : IntervalIntegrable (speed s) volume c d :=
    ((hspeed hs).mono hcdI).intervalIntegrable_of_Icc hcd
  have hlength {c d : ℝ} (hcd : c ≤ d) (hcdI : Icc c d ⊆ I) :
      (fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s) c d).toReal) =ᶠ[𝓝 s₀]
        (fun s ↦ ∫ t in c..d, speed s t) := by
    filter_upwards [hB.mem_nhds hs₀] with s hs
    exact F.pathELength_toReal_eq_integral_speed hcd (hint hs hcd hcdI)
  have hposition : ContinuousOn (Γ s₀) I :=
    (contMDiffOn_positionFamily_of_tangentFamily hG).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hs₀, ht⟩)
  have hlocal (t : Icc a b) : ∃ r : ℝ, 0 < r ∧
      Ioo ((t : ℝ) - r) ((t : ℝ) + r) ⊆ I ∧
      MapsTo (Γ s₀) (Ioo ((t : ℝ) - r) ((t : ℝ) + r))
        (extChartAt 𝓘(ℝ, E) (Γ s₀ t)).source := by
    have hO : IsOpen (I ∩ (Γ s₀) ⁻¹' (extChartAt 𝓘(ℝ, E) (Γ s₀ t)).source) :=
      hposition.isOpen_inter_preimage hI (isOpen_extChartAt_source _)
    have htO : (t : ℝ) ∈ I ∩ (Γ s₀) ⁻¹' (extChartAt 𝓘(ℝ, E) (Γ s₀ t)).source :=
      ⟨hsegment t.property, mem_extChartAt_source _⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO t htO
    have hsub : Ioo ((t : ℝ) - r) ((t : ℝ) + r) ⊆
        I ∩ (Γ s₀) ⁻¹' (extChartAt 𝓘(ℝ, E) (Γ s₀ t)).source := by
      intro u hu
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    exact ⟨r, hr, fun u hu ↦ (hsub hu).1, fun u hu ↦ (hsub hu).2⟩
  choose r hr hsub hmap using hlocal
  let J : Icc a b → Set ℝ := fun t ↦ Ioo ((t : ℝ) - r t) ((t : ℝ) + r t)
  let C : Icc a b → Set (Icc a b) := fun t ↦ Subtype.val ⁻¹' J t
  have hC : ∀ t, IsOpen (C t) := fun t ↦ isOpen_Ioo.preimage continuous_subtype_val
  have hcover : univ ⊆ ⋃ t, C t := by
    intro t _
    apply mem_iUnion.mpr
    refine ⟨t, ?_⟩
    change (t : ℝ) - r t < t ∧ (t : ℝ) < t + r t
    constructor <;> linarith [hr t]
  obtain ⟨τ, hτ₀, hτmono, ⟨m, hm⟩, hτcover⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hC hcover
  have hτI (n : ℕ) : (τ n : ℝ) ∈ I := hsegment (τ n).property
  have hτle (n : ℕ) : (τ n : ℝ) ≤ τ (n + 1) := hτmono (Nat.le_succ n)
  have hpiece (n : ℕ) :
      HasFDerivAt (fun s ↦ ∫ t in (τ n : ℝ)..(τ (n + 1) : ℝ), speed s t)
        (D (τ (n + 1)) - D (τ n)) s₀ := by
    obtain ⟨t, ht⟩ := hτcover n
    have hseg : Icc (τ n : ℝ) (τ (n + 1) : ℝ) ⊆ J t := by
      intro u hu
      let v : Icc a b := ⟨u, (τ n).property.1.trans hu.1, hu.2.trans (τ (n + 1)).property.2⟩
      exact ht (show v ∈ Icc (τ n) (τ (n + 1)) from hu)
    have hd := hF.hasFDerivAt_family_pathELength_mfderiv (Γ s₀ t) hB isOpen_Ioo
      isPreconnected_Ioo (hG.mono (prod_mono Subset.rfl (hsub t))) hs₀ (hτle n)
      hseg (hEL.mono (hsub t)) (hmap t)
    change HasFDerivAt (fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s)
      (τ n : ℝ) (τ (n + 1) : ℝ)).toReal) (D (τ (n + 1)) - D (τ n)) s₀ at hd
    exact hd.congr_of_eventuallyEq (hlength (hτle n) (hseg.trans (hsub t))).symm
  have hsum (n : ℕ) : HasFDerivAt (fun s ↦ ∫ t in a..(τ n : ℝ), speed s t)
      (D (τ n) - D a) s₀ := by
    induction n with
    | zero =>
      rw [hτ₀]
      simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) s₀
    | succ n ih =>
      have hd := ih.add (hpiece n)
      have hlin : (D (τ n) - D a) + (D (τ (n + 1)) - D (τ n)) =
          D (τ (n + 1)) - D a := by abel
      rw [hlin] at hd
      apply hd.congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hs₀] with s hs
      symm
      apply intervalIntegral.integral_add_adjacent_intervals
      · exact hint hs (τ n).property.1 (fun t ht ↦
          hsegment ⟨ht.1, ht.2.trans (τ n).property.2⟩)
      · exact hint hs (hτle n) (fun t ht ↦
          hsegment ⟨(τ n).property.1.trans ht.1, ht.2.trans (τ (n + 1)).property.2⟩)
  have hd := hsum m
  rw [hm m le_rfl] at hd
  exact hd.congr_of_eventuallyEq (hlength hab hsegment)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
