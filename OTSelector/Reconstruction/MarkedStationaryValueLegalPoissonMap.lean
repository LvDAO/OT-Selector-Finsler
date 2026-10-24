import OTSelector.Reconstruction.MarkedStationaryValueLegalPoisson
import Mathlib.Probability.Independence.InfinitePi

/-!
# Exact mark pushforwards for the legal Poisson pressure

Auxiliary RN types can be forgotten without changing positions or Poisson counts.
The pushforward of the entire two-color marked cloud is proved from the original
iid product law. The literal legal finite value and legal cardinality commute
with this map, and integration identifies the actual legal pressures exactly.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

variable {q : ℕ} {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

/-- Change only the original marks, preserving every position and the Poisson count. -/
def mapMarkedCloud (f : A → C) (z : MarkedCloudSpace q A) : MarkedCloudSpace q C :=
  (z.1, fun i ↦ ((z.2 i).1, f (z.2 i).2))

theorem measurable_mapMarkedCloud {f : A → C} (hf : Measurable f) :
    Measurable (mapMarkedCloud (q := q) f) := by
  unfold mapMarkedCloud
  fun_prop

/-- The iid marked law transforms exactly by the mark pushforward. -/
theorem map_markedSeqLaw_marks (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (γ : Measure C) [IsProbabilityMeasure γ]
    {f : A → C} (hf : Measurable f) (hγ : α.map f = γ) :
    (markedSeqLaw q A α).map (fun seq i ↦ ((seq i).1, f (seq i).2)) =
      markedSeqLaw q C γ := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  unfold markedSeqLaw
  change (Measure.infinitePi (fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α)).map
    (fun seq i ↦ (Prod.map id f) (seq i)) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α)
    (f := fun _ : ℕ ↦ Prod.map id f) (fun _ ↦ measurable_id.prodMap hf)]
  congr 1
  funext i
  rw [← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id, hγ]

/-- The actual marked Poisson law transforms exactly by the mark pushforward. -/
theorem map_markedPoissonLaw_marks (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (γ : Measure C) [IsProbabilityMeasure γ]
    {f : A → C} (hf : Measurable f) (hγ : α.map f = γ) (r : ℝ≥0) :
    (markedPoissonLaw q A α r).map (mapMarkedCloud f) =
      markedPoissonLaw q C γ r := by
  unfold markedPoissonLaw mapMarkedCloud
  change ((poissonMeasure r).prod (markedSeqLaw q A α)).map
    (Prod.map id (fun seq i ↦ ((seq i).1, f (seq i).2))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    map_markedSeqLaw_marks q α γ hf hγ]

/-- Both independent colors retain their exact original pushforward mark laws. -/
theorem map_twoMarkedCloudLaw_marks (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ) (r : ℝ≥0) :
    (twoMarkedCloudLaw q A B α β r).map
      (Prod.map (mapMarkedCloud f) (mapMarkedCloud g)) =
        twoMarkedCloudLaw q C D γ δ r := by
  unfold twoMarkedCloudLaw
  rw [← Measure.map_prod_map _ _ (measurable_mapMarkedCloud hf) (measurable_mapMarkedCloud hg),
    map_markedPoissonLaw_marks q α γ hf hγ r, map_markedPoissonLaw_marks q β δ hg hδ r]

omit [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] in
/-- Pulling clocks and kernels back through mark maps preserves the literal finite legal value. -/
theorem legalMarkedTilted_mapMarkedCloud (q : ℕ)
    (f : A → C) (g : B → D) (sourceClock : C → ℝ) (targetClock : D → ℝ)
    (r : ℝ) (kin : C → D → (Fin q → ℝ) → ℝ) (probe : C → D → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    legalMarkedTilted q sourceClock targetClock r kin probe t
      (mapMarkedCloud f ω.1, mapMarkedCloud g ω.2) =
        legalMarkedTilted q (sourceClock ∘ f) (targetClock ∘ g) r
          (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) t ω := rfl


omit [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] in
/-- Pulling clocks back preserves the literal legal matching cardinality. -/
theorem legalMarkedMaximumCard_mapMarkedCloud (q : ℕ)
    (f : A → C) (g : B → D) (sourceClock : C → ℝ) (targetClock : D → ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    legalMarkedMaximumCard q sourceClock targetClock
      (mapMarkedCloud f ω.1, mapMarkedCloud g ω.2) =
        legalMarkedMaximumCard q (sourceClock ∘ f) (targetClock ∘ g) ω := rfl

/-- Auxiliary marks can be forgotten at the actual legal pressure level, with
all positions, clocks and the finite maximum-cardinality problem preserved. -/
theorem legalMarkedPressure_eq_pullback (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ)
    {sourceClock : C → ℝ} {targetClock : D → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (r : ℝ≥0) (kin : C → D → (Fin q → ℝ) → ℝ)
    (hkin : Measurable (Function.uncurry (fun p : C × D ↦ kin p.1 p.2)))
    (probe : C → D → ℝ) (hp : Measurable (Function.uncurry probe)) (t : ℝ) :
    legalMarkedPressure q sourceClock targetClock γ δ r kin probe t =
      legalMarkedPressure q (sourceClock ∘ f) (targetClock ∘ g) α β r
        (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) t := by
  have hm := map_twoMarkedCloudLaw_marks q α β γ δ hf hg hγ hδ r
  unfold legalMarkedPressure
  rw [← hm, integral_map
    ((measurable_mapMarkedCloud hf).prodMap (measurable_mapMarkedCloud hg)).aemeasurable
    (measurable_legalMarkedTilted q hs ht hkin hp r t).aestronglyMeasurable]
  rfl

end OTSelector.Reconstruction
