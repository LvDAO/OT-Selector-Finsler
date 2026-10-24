import OTSelector.MeasureTheory.DyadicClockCells
import OTSelector.Probability.BirthActualProfileSummability
import OTSelector.MeasureTheory.Lp.SummableSeries

/-! Double-dyadic birth traffic is L2 from its actual finite-level norm
bounds. The count threshold and summable majorant are chosen internally.
The argument is independent of the endpoint, current, geometric frame or law
construction used to produce the input level estimates. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000

/-- Full physical birth-level bounds above a fixed actual count threshold imply
L2 and almost sure absolute convergence of the literal double-dyadic sum.
The interleaved thresholds and the summable majorant are chosen internally. -/
theorem memLp_original_full_birth_double_tsum_of_level_norm_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K₀ q ε E A Btail : ℝ} (hK₀ : 0 ≤ K₀) (hq : 0 < q) (hε : 0 < ε) (hE : 1 ≤ E)
    (hA : 0 ≤ A) (hBtail : 0 ≤ Btail) (rank : ℕ)
    (level : (ℕ × ℕ) → Ω → ℝ) (hLp : ∀ z, MemLp (level z) 2 P)
    (hlevel : ∀ z : ℕ × ℕ, ∀ {K : ℝ}, K₀ ≤ K →
      eLpNorm (level z) 2 P ≤ ENNReal.ofReal
        (A * Real.sqrt (K * E) *
          ((birthDyadicShellScale ε z.1) ^ (1 / (2 * q)) *
              Real.sqrt ((birthDyadicElapsedScale ε z.1 z.2) /
                (birthDyadicShellScale ε z.1)) +
            (birthDyadicShellScale ε z.1) ^
                (if rank=0 then (3/8:ℝ) else (rank:ℝ)/8) *
              ((birthDyadicElapsedScale ε z.1 z.2) / (birthDyadicShellScale ε z.1)) ^
                (if rank=0 then (3/28:ℝ) else (rank:ℝ)/(4*(3*(rank:ℝ)+4)))) +
          Btail * ((2 : ℝ) ^ z.2 * Real.exp (-K/4)))) :
    MemLp (fun scene ↦ ∑' z : ℕ × ℕ, level z scene) 2 P ∧
      Summable (fun z : ℕ × ℕ ↦ (eLpNorm (level z) 2 P).toReal) ∧
      ∀ᵐ scene ∂P, Summable (fun z : ℕ × ℕ ↦ ‖level z scene‖) := by
  obtain ⟨C,hC,hsum⟩ := exists_summable_original_birth_profile_with_constants
    (K₀:=K₀) (E:=E) (t:=ε/2) (q:=q) (c:=1/4) (A:=A) (B:=Btail)
    hK₀ (by linarith) (by positivity) hq (by norm_num) hA hBtail rank
  let K := fun z : ℕ × ℕ ↦ interleavedLevelThreshold K₀ C z.1 z.2
  let β := if rank=0 then (3/8:ℝ) else (rank:ℝ)/8
  let γ := if rank=0 then (3/28:ℝ) else (rank:ℝ)/(4*(3*(rank:ℝ)+4))
  let B := fun z : ℕ × ℕ ↦
    A * (Real.sqrt (K z*E) *
      (((ε/2)/(2:ℝ)^z.1)^(1/(2*q)) * (1/(2:ℝ)^z.2)^(1/2:ℝ) +
        ((ε/2)/(2:ℝ)^z.1)^β * (1/(2:ℝ)^z.2)^γ)) +
      Btail * ((2:ℝ)^z.2 * Real.exp (-(1/4:ℝ)*K z))
  have hB : Summable B := hsum
  have hB0 : ∀ z, 0 ≤ B z := by intro z; dsimp only [B]; positivity
  have hK : ∀ z, K₀ ≤ K z := by
    intro z
    dsimp only [K,interleavedLevelThreshold]
    have hpos : 0 ≤ C * ((z.1 : ℝ) + (z.2 : ℝ) + 1) := by positivity
    linarith
  have hbound : ∀ z, eLpNorm (level z) 2 P ≤ ENNReal.ofReal (B z) := by
    intro z
    have hn := hlevel z (hK z)
    have ht : 0 < birthDyadicShellScale ε z.1 := birthDyadicShellScale_pos hε z.1
    have hscale : birthDyadicShellScale ε z.1 = (ε/2)/(2:ℝ)^z.1 := by
      dsimp only [birthDyadicShellScale]
      rw [pow_succ]
      field_simp
    have hratio : birthDyadicElapsedScale ε z.1 z.2/birthDyadicShellScale ε z.1 =
        1/(2:ℝ)^z.2 := by
      dsimp only [birthDyadicElapsedScale]
      field_simp
    apply hn.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [B, β, γ]
    rw [hratio, hscale]
    have hexp : -(K z)/4 = -(1/4:ℝ)*K z := by ring
    rw [hexp]
    simp only [Real.sqrt_eq_rpow, mul_assoc]
    exact le_rfl
  have hnorm : Summable (fun z ↦ (eLpNorm (level z) 2 P).toReal) :=
    hB.of_nonneg_of_le (fun _ ↦ ENNReal.toReal_nonneg)
      (fun z ↦ ENNReal.toReal_le_of_le_ofReal (hB0 z) (hbound z))
  have hout := memLp_tsum_of_summable_level_bound P level hLp B hB hB0 hbound
  exact ⟨hout.1,hnorm,hout.2.2⟩

/-- Actual rank-dependent birth level bounds, including their original
count-bad remainder, imply L2 and almost sure absolute convergence of the
literal double-dyadic sum. No external summability bound is assumed. -/
theorem memLp_original_birth_double_tsum_of_level_norm_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q ε E A Btail : ℝ} (hq : 0 < q) (hε : 0 < ε) (hE : 1 ≤ E)
    (hA : 0 ≤ A) (hBtail : 0 ≤ Btail) (rank : ℕ)
    (level : (ℕ × ℕ) → Ω → ℝ) (hLp : ∀ z, MemLp (level z) 2 P)
    (hlevel : ∀ z : ℕ × ℕ, ∀ {K : ℝ}, 0 ≤ K →
      eLpNorm (level z) 2 P ≤ ENNReal.ofReal
        ((A * Real.sqrt K * Real.sqrt E) *
          ((birthDyadicShellScale ε z.1) ^ (if rank=0 then (3/8:ℝ) else (rank:ℝ)/8) *
            ((birthDyadicElapsedScale ε z.1 z.2) / (birthDyadicShellScale ε z.1)) ^
              (if rank=0 then (3/28:ℝ) else (rank:ℝ)/(4*(3*(rank:ℝ)+4)))) +
          (dyadicBirthBandCount z.2 : ℝ) * (Btail * Real.exp (-K/4)))) :
    MemLp (fun scene ↦ ∑' z : ℕ × ℕ, level z scene) 2 P ∧
      Summable (fun z : ℕ × ℕ ↦ (eLpNorm (level z) 2 P).toReal) ∧
      ∀ᵐ scene ∂P, Summable (fun z : ℕ × ℕ ↦ ‖level z scene‖) := by
  apply memLp_original_full_birth_double_tsum_of_level_norm_bounds P
    (K₀ := 0) (Btail := 8 * Btail) (by norm_num) hq hε hE hA (by positivity)
    rank level hLp
  intro z K hK
  have hn := hlevel z hK
  apply hn.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.sqrt_mul hK]
  have ht := birthDyadicShellScale_pos hε z.1
  have hpos : 0 ≤ A * Real.sqrt K * Real.sqrt E *
      ((birthDyadicShellScale ε z.1) ^ (1 / (2 * q)) *
        Real.sqrt (birthDyadicElapsedScale ε z.1 z.2 / birthDyadicShellScale ε z.1)) :=
    by positivity
  simp only [dyadicBirthBandCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  nlinarith

end OTSelector.Reconstruction
