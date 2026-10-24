import OTSelector.Reconstruction.FinslerRelativeLawOriginalRawClassValue
import OTSelector.Probability.HaarAffineCube

/-! Exact true-coordinate restoration and its measurable finite legal value. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Restoring the original affine coordinates cancels the actual normalization
at every point, including points outside the selected cell. -/
theorem affineMarkedPoint_affineHaarCubeCoord_restore
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {A : Type*} (p : E × A) :
    affineMarkedPoint origin side (Prod.map (affineHaarCubeCoord e origin side) id p) =
      Prod.map e id p := by
  apply Prod.ext
  · funext l
    have hs : (side : ℝ) ≠ 0 := by exact_mod_cast hside.ne'
    change origin l + (side : ℝ) * ((side : ℝ)⁻¹ * (e p.1 l - origin l)) = e p.1 l
    field_simp
    ring
  · rfl

/-- The original enumeration and count are unchanged under normalization and
restoration of every used coordinate. -/
theorem mapBlockData_affineHaarCubeCoord_restore
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {A : Type*} (d : BlockData (E × A)) :
    mapBlockData (affineMarkedPoint origin side)
      (mapBlockData (Prod.map (affineHaarCubeCoord e origin side) id) d) =
      mapBlockData (Prod.map e id) d := by
  cases d with
  | mk m x =>
    dsimp only [mapBlockData]
    congr 1
    funext i
    exact affineMarkedPoint_affineHaarCubeCoord_restore e origin hside (x i)

/-- The true affine physical prefix value is globally measurable. -/
theorem measurable_unclampedBlockLegalTilted_affine (q : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B]
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ) {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (origin : Fin q → ℝ) (side tilt : ℝ) :
    Measurable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin probe tilt
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)) := by
  have hraw : Measurable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin probe tilt d.1 d.2) :=
    measurable_unclampedBlockLegalTilted q hs ht r hk hp tilt
  have hcoord : Measurable (Prod.map
      (mapBlockData (affineMarkedPoint (A := A) origin side))
      (mapBlockData (affineMarkedPoint (A := B) origin side))) :=
    (measurable_mapBlockData (measurable_affineMarkedPoint origin side)).prodMap
      (measurable_mapBlockData (measurable_affineMarkedPoint origin side))
  have heq : (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin probe tilt
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)) =
      (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
        unclampedBlockLegalTilted q source target r kin probe tilt d.1 d.2) ∘
      Prod.map (mapBlockData (affineMarkedPoint (A := A) origin side))
        (mapBlockData (affineMarkedPoint (A := B) origin side)) := by
    funext d
    rfl
  rw [heq]
  exact hraw.comp hcoord

end OTSelector.Reconstruction
