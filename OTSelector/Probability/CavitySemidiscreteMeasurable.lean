import OTSelector.Transport.Semidiscrete.OppositeOptima

/-!
# Jointly measurable allocation factors

Conditioning on the actual cavity mass statistic factors the entire allocation, not
only one scalar test. Fiber constancy is allowed to hold almost everywhere in the source.
Kernel integration and Fubini then give one jointly measurable version of all coefficients.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {W B S : Type*} [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
  [MeasurableSpace B] [MeasurableEq B] [MeasurableSpace S] {m : ℕ}

/-- Almost everywhere fiber-constant allocation functions admit a jointly measurable factor,
with an actual original allocation representative on almost every statistical fiber. -/
theorem exists_measurable_allocation_of_fiber_constancy
    (P : Measure W) [IsProbabilityMeasure P] (μ : Measure S) [SFinite μ]
    (f : W → B) (hf : Measurable f)
    (a : W × S → Fin (m + 1) → ℝ) (ha : ∀ j, Measurable (fun z ↦ a z j))
    (hconst : ∀ w v, f w = f v → (fun s ↦ a (w, s)) =ᵐ[μ] fun s ↦ a (v, s)) :
    ∃ A : B × S → Fin (m + 1) → ℝ,
      (∀ j, Measurable (fun z ↦ A z j)) ∧
      ∀ᵐ b ∂P.map f, ∃ w, f w = b ∧ (fun s ↦ A (b, s)) =ᵐ[μ] fun s ↦ a (w, s) := by
  let κ := condDistrib (id : W → W) f P
  let A : B × S → Fin (m + 1) → ℝ := fun z j ↦ ∫ w, a (w, z.2) j ∂κ z.1
  have hA j : Measurable (fun z ↦ A z j) := by
    have hm : Measurable (fun q : (B × S) × W ↦ a (q.2, q.1.2) j) :=
      (ha j).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact (hm.stronglyMeasurable.integral_kernel_prod_right'
      (κ := κ.prodMkRight S)).measurable
  have hsupp : ∀ᵐ b ∂P.map f, ∀ᵐ w ∂κ b, f w = b := by
    apply Measure.ae_ae_of_ae_compProd (μ := P.map f) (κ := κ)
      (p := fun q : B × W ↦ f q.2 = q.1)
    change ∀ᵐ q ∂((P.map f) ⊗ₘ condDistrib id f P), f q.2 = q.1
    rw [compProd_map_condDistrib aemeasurable_id]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst)).mpr
    exact Eventually.of_forall fun _ ↦ rfl
  refine ⟨A, hA, ?_⟩
  filter_upwards [hsupp] with b hb
  obtain ⟨w, hw⟩ := hb.exists
  refine ⟨w, hw, ?_⟩
  have hj (j : Fin (m + 1)) : ∀ᵐ s ∂μ, A (b, s) j = a (w, s) j := by
    have hm : MeasurableSet {q : W × S | a q j = a (w, q.2) j} :=
      measurableSet_eq_fun (ha j)
        ((ha j).comp (measurable_const.prodMk measurable_snd))
    have heq : ∀ᵐ v ∂κ b, ∀ᵐ s ∂μ, a (v, s) j = a (w, s) j := by
      filter_upwards [hb] with v hv
      exact (hconst v w (hv.trans hw.symm)).mono fun s hs ↦ congrFun hs j
    have hswap := (Measure.ae_ae_comm hm).mp heq
    filter_upwards [hswap] with s hs
    change (∫ v, a (v, s) j ∂κ b) = a (w, s) j
    rw [integral_congr_ae hs]
    simp
  filter_upwards [ae_all_iff.mpr hj] with s hs
  exact funext hs

/-- The same factorization uses only a full-measure set of good original environments.
No measurability hypothesis on the good predicate is needed. -/
theorem exists_measurable_allocation_of_ae_fiber_constancy
    (P : Measure W) [IsProbabilityMeasure P] (μ : Measure S) [SFinite μ]
    (f : W → B) (hf : Measurable f)
    (a : W × S → Fin (m + 1) → ℝ) (ha : ∀ j, Measurable (fun z ↦ a z j))
    (Good : W → Prop) (hgood : ∀ᵐ w ∂P, Good w)
    (hconst : ∀ w, Good w → ∀ v, f w = f v →
      (fun s ↦ a (w, s)) =ᵐ[μ] fun s ↦ a (v, s)) :
    ∃ A : B × S → Fin (m + 1) → ℝ,
      (∀ j, Measurable (fun z ↦ A z j)) ∧
      ∀ᵐ b ∂P.map f, ∃ w, Good w ∧ f w = b ∧
        (fun s ↦ A (b, s)) =ᵐ[μ] fun s ↦ a (w, s) := by
  let κ := condDistrib (id : W → W) f P
  let A : B × S → Fin (m + 1) → ℝ := fun z j ↦ ∫ w, a (w, z.2) j ∂κ z.1
  have hA j : Measurable (fun z ↦ A z j) := by
    have hm : Measurable (fun q : (B × S) × W ↦ a (q.2, q.1.2) j) :=
      (ha j).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact (hm.stronglyMeasurable.integral_kernel_prod_right'
      (κ := κ.prodMkRight S)).measurable
  have hsupp : ∀ᵐ b ∂P.map f, ∀ᵐ w ∂κ b, f w = b := by
    apply Measure.ae_ae_of_ae_compProd (μ := P.map f) (κ := κ)
      (p := fun q : B × W ↦ f q.2 = q.1)
    change ∀ᵐ q ∂((P.map f) ⊗ₘ condDistrib id f P), f q.2 = q.1
    rw [compProd_map_condDistrib aemeasurable_id]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst)).mpr
    exact Eventually.of_forall fun _ ↦ rfl
  have hgoodκ : ∀ᵐ b ∂P.map f, ∀ᵐ w ∂κ b, Good w := by
    apply Measure.ae_ae_of_ae_compProd (μ := P.map f) (κ := κ)
      (p := fun q : B × W ↦ Good q.2)
    have hmap : ((P.map f) ⊗ₘ κ).map Prod.snd = P := by
      change ((P.map f) ⊗ₘ κ).snd = P
      rw [Measure.snd_compProd]
      change condDistrib id f P ∘ₘ (P.map f) = P
      rw [condDistrib_comp_map hf.aemeasurable aemeasurable_id, Measure.map_id]
    exact (show MeasurePreserving Prod.snd ((P.map f) ⊗ₘ κ) P from
      ⟨measurable_snd, hmap⟩).quasiMeasurePreserving.ae hgood
  refine ⟨A, hA, ?_⟩
  filter_upwards [hsupp, hgoodκ] with b hb hgb
  obtain ⟨w, hw, hgw⟩ := (hb.and hgb).exists
  refine ⟨w, hgw, hw, ?_⟩
  have hj (j : Fin (m + 1)) : ∀ᵐ s ∂μ, A (b, s) j = a (w, s) j := by
    have hm : MeasurableSet {q : W × S | a q j = a (w, q.2) j} :=
      measurableSet_eq_fun (ha j)
        ((ha j).comp (measurable_const.prodMk measurable_snd))
    have heq : ∀ᵐ v ∂κ b, ∀ᵐ s ∂μ, a (v, s) j = a (w, s) j := by
      filter_upwards [hb] with v hv
      exact (hconst w hgw v (hw.trans hv.symm)).symm.mono fun s hs ↦ congrFun hs j
    have hswap := (Measure.ae_ae_comm hm).mp heq
    filter_upwards [hswap] with s hs
    change (∫ v, a (v, s) j ∂κ b) = a (w, s) j
    rw [integral_congr_ae hs]
    simp
  filter_upwards [ae_all_iff.mpr hj] with s hs
  exact funext hs

end OTSelector.Probability
