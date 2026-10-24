import OTSelector.Reconstruction.FinslerConcreteUpperAllowedInverseCore

/-! A finite family of actual original-index cores pays its physical energy
once. Fine-class augmentation only multiplies the genuine source deficiencies. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {m n : ℕ}

/-- Inactive original source vertices contribute no legal cardinality. -/
theorem legalMaximumCard_le_active_source_card
    (allowed : Finset (Fin m × Fin n)) (active : Fin m → Prop)
    (hactive : ∀ e ∈ allowed, active e.1) :
    legalMaximumCard allowed ≤ (Finset.univ.filter active).card := by
  classical
  obtain ⟨σ, hlegal, hcard⟩ := exists_legalMaximumCard allowed
  rw [← hcard, ← σ.card_rows]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive e (hlegal he)⟩

/-- The actual family comparison preserves one total physical core energy.
The finite family and fine class counts appear only in a source-defect price. -/
theorem sum_legalMaximumValue_le_inverse_relative_cores
    {C : Type*} [Fintype C] {J : C → Type*} [∀ c, Fintype (J c)]
    (allowed : C → Finset (Fin m × Fin n))
    (active : C → Fin m → Prop)
    (hactive : ∀ c e, e ∈ allowed c → active c e.1)
    (σ : C → OTSelector.PartialMatching m n) (hσ : ∀ c, IsLegal (allowed c) (σ c))
    (sourceClass : ∀ c, Fin m → J c) (sourceAllows : ∀ c, J c → Fin n → Prop)
    (hallowed : ∀ c i j, (i,j) ∈ allowed c ↔ sourceAllows c (sourceClass c i) j)
    (physical frozen probe : C → Fin m → Fin n → ℝ)
    {ρ G : ℝ} (hρ : ρ < 1) (hG : 0 ≤ G)
    (edgeBound : C → ℝ) (hB : ∀ c, 0 ≤ edgeBound c)
    (hrelative : ∀ c e, e ∈ (σ c).edges →
      |physical c e.1 e.2 - frozen c e.1 e.2| ≤ ρ * frozen c e.1 e.2)
    (hprobe : ∀ c i j, (i,j) ∈ allowed c → |probe c i j| ≤ G) (tilt : ℝ)
    (hedge : ∀ c i j, (i,j) ∈ allowed c →
      |frozen c i j + tilt * probe c i j| ≤ edgeBound c) :
    (∑ c, legalMaximumValue (allowed c) (fun i j ↦ frozen c i j + tilt * probe c i j)) ≤
      (∑ c, (σ c).cost (physical c)) / (1 - ρ) +
      (∑ c, ((σ c).card : ℝ)) * (|tilt| * G) +
      (∑ c, (2 * (Fintype.card (J c) : ℝ) + 1) * edgeBound c) *
        (∑ c, (((Finset.univ.filter (active c)).card : ℝ) - ((σ c).card : ℝ))) := by
  classical
  let price : ℝ := ∑ c, (2 * (Fintype.card (J c) : ℝ) + 1) * edgeBound c
  have hp : 0 ≤ price := Finset.sum_nonneg fun c _ ↦ mul_nonneg (by positivity) (hB c)
  have hprice (c) : (2 * (Fintype.card (J c) : ℝ) - 1) * edgeBound c ≤ price := by
    calc _ ≤ (2 * (Fintype.card (J c) : ℝ) + 1) * edgeBound c :=
          mul_le_mul_of_nonneg_right (by linarith) (hB c)
      _ ≤ price := by
        change _ ≤ ∑ d, (2 * (Fintype.card (J d) : ℝ) + 1) * edgeBound d
        exact Finset.single_le_sum
          (f := fun d : C ↦ (2 * (Fintype.card (J d) : ℝ) + 1) * edgeBound d)
          (fun d _ ↦ mul_nonneg (by positivity) (hB d)) (Finset.mem_univ c)
  have hcard (c) := card_le_legalMaximumCard (hσ c)
  have hdef (c) : ((legalMaximumCard (allowed c) - (σ c).card : ℕ) : ℝ) ≤
      ((Finset.univ.filter (active c)).card : ℝ) - ((σ c).card : ℝ) := by
    rw [Nat.cast_sub (hcard c)]
    exact sub_le_sub_right (Nat.cast_le.mpr
      (legalMaximumCard_le_active_source_card (allowed c) (active c) (hactive c))) _
  have hvalue (c) := legalMaximumValue_le_inverse_relative_core_of_allowed
    (allowed c) (σ c) (hσ c) (sourceClass c) (sourceAllows c) (hallowed c)
    (physical c) (frozen c) (probe c) hρ hG (hB c) (hrelative c) (hprobe c) tilt (hedge c)
  have hterm (c) : legalMaximumValue (allowed c) (fun i j ↦ frozen c i j + tilt * probe c i j) ≤
      (σ c).cost (physical c) / (1 - ρ) + ((σ c).card : ℝ) * (|tilt| * G) +
        price * (((Finset.univ.filter (active c)).card : ℝ) - ((σ c).card : ℝ)) := by
    refine (hvalue c).trans (add_le_add (le_refl _) ?_)
    calc _ ≤ ((legalMaximumCard (allowed c) - (σ c).card : ℕ) : ℝ) * price :=
          mul_le_mul_of_nonneg_left (hprice c) (Nat.cast_nonneg _)
      _ ≤ _ := (mul_le_mul_of_nonneg_right (hdef c) hp).trans_eq (mul_comm _ _)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hterm c)
  simpa only [Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_mul,
    ← Finset.mul_sum, price] using hsum

/-- The concrete gated class graph needs no row-class encoding premise.
Original inactive indices remain in place and carry the extra none class. -/
theorem sum_gatedClassValue_le_inverse_relative_cores
    {C : Type*} [Fintype C] {J : C → Type*} [∀ c, Fintype (J c)]
    (sourceClass : ∀ c, Fin m → J c) (targetClass : ∀ c, Fin n → J c)
    (relation : ∀ c, J c → J c → Prop)
    (activeS : C → Fin m → Prop) (activeT : C → Fin n → Prop)
    (σ : C → OTSelector.PartialMatching m n)
    (hσ : ∀ c, IsLegal (Finset.univ.filter (fun e : Fin m × Fin n ↦
      activeS c e.1 ∧ activeT c e.2 ∧ relation c (sourceClass c e.1) (targetClass c e.2))) (σ c))
    (physical frozen probe : C → Fin m → Fin n → ℝ)
    {ρ G : ℝ} (hρ : ρ < 1) (hG : 0 ≤ G)
    (edgeBound : C → ℝ) (hB : ∀ c, 0 ≤ edgeBound c)
    (hrelative : ∀ c e, e ∈ (σ c).edges →
      |physical c e.1 e.2 - frozen c e.1 e.2| ≤ ρ * frozen c e.1 e.2)
    (hprobe : ∀ c i j, activeS c i → activeT c j →
      relation c (sourceClass c i) (targetClass c j) → |probe c i j| ≤ G) (tilt : ℝ)
    (hedge : ∀ c i j, activeS c i → activeT c j →
      relation c (sourceClass c i) (targetClass c j) →
      |frozen c i j + tilt * probe c i j| ≤ edgeBound c) :
    (∑ c, legalMaximumValue (Finset.univ.filter (fun e : Fin m × Fin n ↦
      activeS c e.1 ∧ activeT c e.2 ∧ relation c (sourceClass c e.1) (targetClass c e.2)))
      (fun i j ↦ frozen c i j + tilt * probe c i j)) ≤
      (∑ c, (σ c).cost (physical c)) / (1 - ρ) +
      (∑ c, ((σ c).card : ℝ)) * (|tilt| * G) +
      (∑ c, (2 * ((Fintype.card (J c) : ℝ) + 1) + 1) * edgeBound c) *
        (∑ c, (((Finset.univ.filter (activeS c)).card : ℝ) - ((σ c).card : ℝ))) := by
  classical
  let allowed := fun c ↦ Finset.univ.filter (fun e : Fin m × Fin n ↦
    activeS c e.1 ∧ activeT c e.2 ∧ relation c (sourceClass c e.1) (targetClass c e.2))
  let cls := fun c i ↦ if activeS c i then some (sourceClass c i) else none
  let permits := fun c (tag : Option (J c)) j ↦ match tag with
    | none => False
    | some s => activeT c j ∧ relation c s (targetClass c j)
  have hallowed : ∀ c i j, (i,j) ∈ allowed c ↔ permits c (cls c i) j := by
    intro c i j
    by_cases hi : activeS c i <;> simp [allowed, permits, cls, hi]
  have hactive : ∀ c e, e ∈ allowed c → activeS c e.1 :=
    fun c e he ↦ (Finset.mem_filter.mp he).2.1
  have hprobe' : ∀ c i j, (i,j) ∈ allowed c → |probe c i j| ≤ G := by
    intro c i j hij
    obtain ⟨hs,ht,hr⟩ := (Finset.mem_filter.mp hij).2
    exact hprobe c i j hs ht hr
  have hedge' : ∀ c i j, (i,j) ∈ allowed c →
      |frozen c i j + tilt * probe c i j| ≤ edgeBound c := by
    intro c i j hij
    obtain ⟨hs,ht,hr⟩ := (Finset.mem_filter.mp hij).2
    exact hedge c i j hs ht hr
  have h := sum_legalMaximumValue_le_inverse_relative_cores allowed activeS hactive σ hσ cls permits
    hallowed physical frozen probe hρ hG edgeBound hB hrelative hprobe' tilt hedge'
  simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one] using h

end OTSelector.Reconstruction.PartialMatching
