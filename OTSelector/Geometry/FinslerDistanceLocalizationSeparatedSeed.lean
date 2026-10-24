import OTSelector.Geometry.Finsler.CovectorNormalization
import OTSelector.Geometry.FinslerDistanceLocalizationLevelSeed

/-!
# Whole-seed quadratic distance upper bounds for separated times

Compactness of the actual complete-flow image controls large label separations.
Together with the derived path estimate, a positive time gap gives one quadratic
upper constant for every endpoint pair of the same compact level seed, including
auxiliary endpoints and folds. No almost-everywhere Taylor core is used.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every actual compact convex C1,1 level seed has one quadratic upper constant
on a bounded time range with a prescribed positive separation. All label pairs
are included; the complete auxiliary flow may have folds. -/
theorem exists_uniform_separated_level_seed_distance_upper
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hDG : LipschitzWith L (fderiv ℝ G))
    {K : Set W} (hK : IsCompact K) (hconv : Convex ℝ K)
    {σ : W → E} {B : ℝ≥0} (hσ : LipschitzOnWith B σ K)
    (hlegal : ∀ w ∈ K, (σ w, fderiv ℝ G (σ w)) ∈ eL.target)
    {c : ℝ} (hlevel : ∀ w ∈ K, G (σ w) = c) (lo hi : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    let X := fun w t ↦ Phi (F.covectorNormalization old eL (1 / 2)
      (σ w, fderiv ℝ G (σ w))) t
    ∃ C > 0, ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ,
      lo ≤ a → b ≤ hi → δ ≤ b - a →
      (F.lengthEDist (X x a) (X y b)).toReal - (b - a) ≤ C * ‖y - x‖ ^ 2 := by
  let : MetricSpace M := F.metricSpace
  let q := fun w ↦ (σ w, fderiv ℝ G (σ w))
  let N := F.covectorNormalization old eL (1 / 2)
  let f := fun q : (E × E) × ℝ ↦ Phi q.1 q.2
  have hq : LipschitzOnWith (max B (L * B)) q K := hσ.prodMk (hDG.comp_lipschitzOnWith hσ)
  have hP : IsCompact (q '' K) := hK.image_of_continuousOn hq.continuousOn
  have hPU : q '' K ⊆ eL.target := by rintro _ ⟨w, hw, rfl⟩; exact hlegal w hw
  obtain ⟨_, hN, hspec⟩ := hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hNK : IsCompact (N '' (q '' K)) := hP.image_of_continuousOn (hN.continuousOn.mono hPU)
  have hNU : N '' (q '' K) ⊆ chartEnergyDomain old := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hspec p (hPU hp)).2.1
  have hf := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old
    (isOpen_chartEnergyDomain old) hEL (ι := fun z : E × E ↦ z)
    contDiffOn_id (mapsTo_id _) hinit).2
  have hphys : IsCompact (f '' ((N '' (q '' K)) ×ˢ Icc lo hi)) :=
    (hNK.prod isCompact_Icc).image_of_continuousOn (hf.continuousOn.mono
      (fun p hp ↦ ⟨hNU hp.1, mem_univ _⟩))
  obtain ⟨D, hD⟩ := Metric.isBounded_image_iff.mp hphys.isBounded
  obtain ⟨r, hr, C, hC, hb⟩ := hF.exists_uniform_level_seed_distance_upper_local old
    hEL hinit heL hsource hInv hG hDG hK hconv hσ hlegal hlevel lo hi
  let ε := r * δ
  have hε : 0 < ε := mul_pos hr hδ
  let C₀ := max (C / δ) (max D 0 / ε ^ 2)
  have hC₀ : 0 ≤ C₀ := (div_nonneg hC hδ.le).trans (le_max_left _ _)
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro x hx y hy a b hlo hhi hgap
  have hab : a < b := sub_pos.mp (hδ.trans_le hgap)
  have hell : 0 < b - a := sub_pos.mpr hab
  have hC₀' : C₀ ≤ C₀ + 1 := by linarith
  apply le_trans (b := C₀ * ‖y - x‖ ^ 2) _
    (mul_le_mul_of_nonneg_right hC₀' (sq_nonneg _))
  by_cases hn : ‖y - x‖ ≤ ε
  · have hsmall : ‖y - x‖ ≤ r * (b - a) :=
      hn.trans (mul_le_mul_of_nonneg_left hgap hr.le)
    refine (hb x hx y hy a b hab hlo hhi hsmall).trans ?_
    calc
      C * ‖y - x‖ ^ 2 / (b - a) ≤ C * ‖y - x‖ ^ 2 / δ :=
        div_le_div_of_nonneg_left (mul_nonneg hC (sq_nonneg _)) hδ hgap
      _ = (C / δ) * ‖y - x‖ ^ 2 := by ring
      _ ≤ C₀ * ‖y - x‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hn' : ε ≤ ‖y - x‖ := (lt_of_not_ge hn).le
    have hdist := hD (N (q x), a)
      ⟨mem_image_of_mem N (mem_image_of_mem q hx), hlo, hab.le.trans hhi⟩
      (N (q y), b) ⟨mem_image_of_mem N (mem_image_of_mem q hy), hlo.trans hab.le, hhi⟩
    change (F.lengthEDist (Phi (N (q x)) a) (Phi (N (q y)) b)).toReal ≤ D at hdist
    have hD' : D ≤ (max D 0 / ε ^ 2) * ‖y - x‖ ^ 2 := by
      calc
        D ≤ max D 0 := le_max_left _ _
        _ = (max D 0 / ε ^ 2) * ε ^ 2 := by field_simp
        _ ≤ (max D 0 / ε ^ 2) * ‖y - x‖ ^ 2 := mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hε.le (norm_nonneg _)).2 hn')
          (div_nonneg (le_max_right _ _) (sq_nonneg _))
    have hdist' : (F.lengthEDist (Phi (N (q x)) a) (Phi (N (q y)) b)).toReal -
        (b - a) ≤ D := by linarith
    exact hdist'.trans (hD'.trans (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (sq_nonneg _)))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
