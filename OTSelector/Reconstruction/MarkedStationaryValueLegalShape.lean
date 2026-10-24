import OTSelector.Reconstruction.MarkedStationaryValueLegalSubcloudStability
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonBlock
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureRegularity
import OTSelector.Probability.MarkedShapeCloud
import OTSelector.Probability.MarkedCloudCarriers

/-!
# Actual legal shape restriction at a finite cube scale

Fill the spatial holes of a measurable region with the original homogeneous
cloud, then compare by exact original-vertex deletion. The error uses the edge
bound at this finite cube scale. The retained positions and marks stay literal.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The literal legal minimum of the original points in the spatial shape. -/
def shapeLegalMarkedTilted (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (S : Set (Fin q → ℝ)) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  blockLegalTilted q source target r kin g t (shapeCloud S ω.1) (shapeCloud S ω.2)

theorem measurable_shapeLegalMarkedTilted (q : ℕ) [Nonempty A] [Nonempty B]
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) (r : ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (shapeLegalMarkedTilted q source target S r kin g t) := by
  unfold shapeLegalMarkedTilted
  have hcloud : Measurable (fun ω : TwoMarkedCloudSpace q A B ↦
      (shapeCloud S ω.1, shapeCloud S ω.2)) :=
    (((measurable_shapeCloud (A := A) hS).comp measurable_fst).prodMk
      ((measurable_shapeCloud (A := B) hS).comp measurable_snd))
  have h := (measurable_blockLegalTilted q hs ht r hk hg t).comp hcloud
  simpa only [Function.comp_def] using h

/-- Actual subcloud comparison before expectation: the precise missing original
point counts multiply a fixed clock-class factor and the finite cube edge bound. -/
theorem FiniteScalarBins.abs_shapeLegalMarkedTilted_sub_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (S : Set (Fin q → ℝ)) {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (hk : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : ∀ a b, |g a b| ≤ G) (ω : TwoMarkedCloudSpace q A B)
    (hsource : ∀ i : ℕ, source (mSourceMark ω i) ∈ I)
    (hsep : ∀ i j : ℕ, gap ≤ |target (mTargetMark ω j) - source (mSourceMark ω i)|) :
    |shapeLegalMarkedTilted q source target S r kin g t ω -
      legalMarkedTilted q source target r kin g t ω| ≤
      (((mSourceCount ω - (shapeCloud S ω.1).1) +
        (mTargetCount ω - (shapeCloud S ω.2).1) : ℕ) : ℝ) *
        (2 * ((D.count : ℝ) + 1) * (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  let e := shapeCloudEmbedding S ω.1
  let f := shapeCloudEmbedding S ω.2
  let c := fun i : Fin (mSourceCount ω) ↦ fun j : Fin (mTargetCount ω) ↦
    mKineticCost q r kin ω i j + t * mProbe g ω i j
  have hB0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * q) + |t| * G := by positivity
  have hbound := D.abs_legalMaximumValue_subcloud_sub_le hgap
    (fun i : Fin (mSourceCount ω) ↦ source (mSourceMark ω i))
    (fun j : Fin (mTargetCount ω) ↦ target (mTargetMark ω j))
    (fun i ↦ hsource i) (fun i j ↦ hsep i j) e f c hB0
    (fun i j _ ↦ abs_legalMarkedEdge_le q hr hC hk hg t ω i j)
  have hvalue : shapeLegalMarkedTilted q source target S r kin g t ω =
      PartialMatching.legalMaximumValue
        (scalarClockLegalGraph (fun i ↦ source (mSourceMark ω (e i)))
          (fun j ↦ target (mTargetMark ω (f j))))
        (fun i j ↦ c (e i) (f j)) := by
    unfold shapeLegalMarkedTilted blockLegalTilted
    simp only [shapeCloud_point]
    rfl
  rw [hvalue]
  exact hbound

end OTSelector.Reconstruction
