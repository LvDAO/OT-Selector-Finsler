import OTSelector.Reconstruction.FinslerRelativeLawOriginalRawClassValue

/-! The actual seed-displacement canonical competitor is the untruncated finite prefix value. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The original physical comparison's literal seed-difference score has the
same canonical value as its true-coordinate finite prefix. The full original
indices, mask, clock classes and signed probe are all kept exactly. -/
theorem originalRetainedSeedOptimizer_cost_eq_unclampedBlockLegalTilted
    {X Z V A B T : Type*} [AddCommGroup V] [Module ℝ V] {q N : ℕ}
    (a : X → Z) (L : Set Z) (root : X → V) (e : V →ₗ[ℝ] (Fin q → ℝ))
    (markS : X → A) (markT : X → B) (mask : A → B → Prop)
    (source : A → ℝ) (target : B → ℝ)
    (hcode : ∀ j k, mask j k ↔ source j < target k)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let extra := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
        (Fin N → X × Option (Bool × T))) ↦
      Finset.univ.filter (fun p : Fin N × Fin N ↦ mask (markS (cloud.1 p.1).1) (markT (cloud.2 p.2).1))
    let model := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
        (Fin N → X × Option (Bool × T))) j k ↦
      r ^ (2 / (q : ℝ)) * kin (markS (cloud.1 j).1) (markT (cloud.2 k).1)
        (e (root (cloud.2 k).1 - root (cloud.1 j).1)) +
          tilt * probe (markS (cloud.1 j).1) (markT (cloud.2 k).1)
    let dataS := mapBlockData (fun z : X × Option (Bool × T) ↦ (e (root z.1), markS z.1))
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) sample.1)
    let dataT := mapBlockData (fun z : X × Option (Bool × T) ↦ (e (root z.1), markT z.1))
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) sample.2)
    (originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra model () sample).cost (model () sample) =
      unclampedBlockLegalTilted q source target r kin probe tilt dataS dataT := by
  classical
  let readS := fun (_ : Unit) (x : X) ↦ (e (root x), markS x)
  let readT := fun (_ : Unit) (x : X) ↦ (e (root x), markT x)
  let extra := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
      (Fin N → X × Option (Bool × T))) ↦
    Finset.univ.filter (fun p : Fin N × Fin N ↦ mask (markS (cloud.1 p.1).1) (markT (cloud.2 p.2).1))
  let model := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
      (Fin N → X × Option (Bool × T))) j k ↦
    r ^ (2 / (q : ℝ)) * kin (markS (cloud.1 j).1) (markT (cloud.2 k).1)
      (e (root (cloud.2 k).1 - root (cloud.1 j).1)) +
        tilt * probe (markS (cloud.1 j).1) (markT (cloud.2 k).1)
  have hgraph : extra = originalCellScalarClassGraph readS readT
      (fun _ : Unit ↦ source) (fun _ : Unit ↦ target) := by
    funext c cloud
    ext p
    simp only [extra, originalCellScalarClassGraph, scalarClockLegalGraph, Finset.mem_filter,
      Finset.mem_univ, true_and, readS, readT, hcode]
  have hmodel : model = originalCellRawClassScore readS readT (fun _ : Unit ↦ r)
      (fun _ : Unit ↦ kin) (fun _ : Unit ↦ probe) tilt := by
    funext c cloud j k
    dsimp only [model, originalCellRawClassScore, readS, readT]
    rw [map_sub]
    rfl
  dsimp only
  change (originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra model () sample).cost (model () sample) = _
  rw [hgraph, hmodel]
  exact originalRetainedCellOptimizer_raw_model_cost_eq_unclampedBlockLegalTilted a (fun _ : Unit ↦ L)
    readS readT (fun _ : Unit ↦ source) (fun _ : Unit ↦ target) (fun _ : Unit ↦ r)
    (fun _ : Unit ↦ kin) (fun _ : Unit ↦ probe) tilt () sample

end OTSelector.Reconstruction
