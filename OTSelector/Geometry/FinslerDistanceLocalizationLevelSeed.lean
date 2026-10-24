import OTSelector.Geometry.Finsler.CovectorNormalization
import OTSelector.Geometry.FinslerDistanceLocalizationLevelPath
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Quadratic distance control on actual convex C1,1 level seeds

Straight label paths are pushed through the original covector normalization and
complete flow. Their one-dimensional normal cancellation gives the distance
estimate uniformly on a compact convex seed and a fixed bounded time range.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The affine endpoint path has its exact Lipschitz constant and remains in
the same convex label domain. -/
theorem affine_label_path_data {K : Set W} (hK : Convex ℝ K)
    {x y : W} (hx : x ∈ K) (hy : y ∈ K) {a b : ℝ} (hab : a < b) :
    let z := fun t : ℝ ↦ x + ((t - a) / (b - a)) • (y - x)
    z a = x ∧ z b = y ∧ MapsTo z (Icc a b) K ∧
      LipschitzWith ⟨‖y - x‖ / (b - a), div_nonneg (norm_nonneg _) (sub_pos.mpr hab).le⟩ z := by
  dsimp only
  refine ⟨by simp, by simp [sub_ne_zero.mpr hab.ne'], ?_, ?_⟩
  · intro t ht
    exact hK.add_smul_sub_mem hx hy ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right ht.2 a)⟩
  · apply LipschitzWith.of_dist_le_mul
    intro t s
    have heq : (x + ((t - a) / (b - a)) • (y - x)) -
        (x + ((s - a) / (b - a)) • (y - x)) = ((t - s) / (b - a)) • (y - x) := by
      rw [show (t - s) / (b - a) = (t - a) / (b - a) - (s - a) / (b - a) by ring,
        sub_smul]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_pos (sub_pos.mpr hab), Real.dist_eq]
    change |t - s| / (b - a) * ‖y - x‖ ≤ ‖y - x‖ / (b - a) * |t - s|
    exact le_of_eq (by ring)

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- On a compact convex actual level seed, all sufficiently slow straight label
paths satisfy the original distance upper estimate. The same constants work
for every pair of labels and all ordered times in the prescribed time range. -/
theorem exists_uniform_level_seed_distance_upper_local
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
    {c : ℝ} (hlevel : ∀ w ∈ K, G (σ w) = c) (lo hi : ℝ) :
    let X := fun w t ↦ Phi (F.covectorNormalization old eL (1 / 2)
      (σ w, fderiv ℝ G (σ w))) t
    ∃ r > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ,
      a < b → lo ≤ a → b ≤ hi → ‖y - x‖ ≤ r * (b - a) →
      (F.lengthEDist (X x a) (X y b)).toReal - (b - a) ≤
        C * ‖y - x‖ ^ 2 / (b - a) := by
  let q := fun w ↦ (σ w, fderiv ℝ G (σ w))
  have hq : LipschitzOnWith (max B (L * B)) q K := hσ.prodMk (hDG.comp_lipschitzOnWith hσ)
  have hP : IsCompact (q '' K) := hK.image_of_continuousOn hq.continuousOn
  have hPU : q '' K ⊆ eL.target := by rintro _ ⟨w, hw, rfl⟩; exact hlegal w hw
  obtain ⟨A, _, r, hr, C, hb⟩ := hF.exists_uniform_normalized_level_path_upper old
    hEL hinit heL hsource hInv hP hPU hG hDG lo hi
  let k : ℝ := (A : ℝ) * B
  have hk : 0 ≤ k := mul_nonneg A.coe_nonneg B.coe_nonneg
  refine ⟨r / (k + 1), div_pos hr (by positivity), (C : ℝ) * k ^ 2, by positivity, ?_⟩
  intro x hx y hy a b hab hlo hhi hsmall
  let ell := b - a
  have hell : 0 < ell := sub_pos.mpr hab
  let D : ℝ≥0 := ⟨‖y - x‖ / ell, div_nonneg (norm_nonneg _) hell.le⟩
  let z := fun t : ℝ ↦ x + ((t - a) / ell) • (y - x)
  obtain ⟨hza, hzb, hzK, hzLip⟩ := affine_label_path_data hconv hx hy hab
  have hσz : LipschitzOnWith (B * D) (σ ∘ z) (Icc a b) :=
    hσ.comp hzLip.lipschitzOnWith hzK
  have hslow : ((A * (B * D) : ℝ≥0) : ℝ) ≤ r := by
    change (A : ℝ) * ((B : ℝ) * (‖y - x‖ / ell)) ≤ r
    have hnorm : ‖y - x‖ / ell ≤ r / (k + 1) :=
      (div_le_iff₀ hell).2 hsmall
    have hkr : k * (r / (k + 1)) ≤ r := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < k + 1)]
      nlinarith
    calc
      (A : ℝ) * ((B : ℝ) * (‖y - x‖ / ell)) = k * (‖y - x‖ / ell) := by dsimp [k]; ring
      _ ≤ k * (r / (k + 1)) := mul_le_mul_of_nonneg_left hnorm hk
      _ ≤ r := hkr
  have hh := hb hab.le hlo hhi hσz
    (fun s hs ↦ mem_image_of_mem q (hzK hs)) (fun s hs ↦ hlevel (z s) (hzK hs)) hslow
  dsimp only at hh ⊢
  change (F.lengthEDist
    (Phi (F.covectorNormalization old eL (1 / 2) (q (z a))) a)
    (Phi (F.covectorNormalization old eL (1 / 2) (q (z b))) b)).toReal - (b - a) ≤ _ at hh
  have hza' : z a = x := hza
  have hzb' : z b = y := hzb
  rw [hza', hzb'] at hh
  refine hh.trans (le_of_eq ?_)
  change (b - a) * (C : ℝ) * ((A : ℝ) * ((B : ℝ) * (‖y - x‖ / ell))) ^ 2 =
    (C : ℝ) * k ^ 2 * ‖y - x‖ ^ 2 / (b - a)
  dsimp [ell, k]
  field_simp

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
