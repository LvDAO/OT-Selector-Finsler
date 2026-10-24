import OTSelector.Reconstruction.FinslerOriginalKinPairingIdentification

/-!
# Affine seed label readout

This module supplies the last structural fact of the mark lane: on the retained
root family the seed label readout `mark ↦ bW.equivFun (w (a ·))` is affine — a
linear label coordinate plus a constant seed offset.  The predicate
`SeedReadoutAffineOn` records exactly this, and the module composes it with the
affine quadratic readout transfer of `FinslerOriginalKinIdentification` and the
mark-pairing identification of `FinslerOriginalKinPairingIdentification`.

For the actual coefficient-lane definitions the pairing height-slice identification
gives `frozenPhysicalCost z₀ x y = matrixQuadratic (C.matrix z₀ q) (readout (x,y))`,
so once the seed readout is affine (resp. the probe functional is linear in the
readout) the actual `kin`/`g` agree on the retained roots with affine quadratic
(resp. affine) readouts; the transfer theorems below then give
`HasMarkLipschitzConstantsOn` for the actual functions, feeding the mark modulus
transfer `sum_markedEdgeError_le_of_markModulus`.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- On the retained root family `K`, the seed label readout `f` is affine: it
agrees with `L z + c` for a continuous linear label coordinate `L` and a constant
seed offset `c`. -/
def SeedReadoutAffineOn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) {n : Type*} (f : E → n → ℝ) : Prop :=
  ∃ (L : E →L[ℝ] (n → ℝ)) (c : n → ℝ), ∀ z ∈ K, f z = L z + c

/-- **Composition with the affine quadratic readout transfer.**  If the seed
readouts of `kin` and `g` are affine on the retained roots and the two functions
are the frozen quadratic forms of those readouts (the mark-pairing identification
forms), then they have the mark-Lipschitz constants of the mark modulus lane. -/
theorem hasMarkLipschitzConstantsOn_of_seedReadoutAffine {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    {kin g : E → ℝ} (A B : Matrix n n ℝ) {readsk readsg : E → n → ℝ}
    (hreadk : SeedReadoutAffineOn E K readsk)
    (hreadg : SeedReadoutAffineOn E K readsg)
    (hkin : ∀ z ∈ K, kin z = matrixQuadratic A (readsk z))
    (hg : ∀ z ∈ K, g z = matrixQuadratic B (readsg z)) :
    HasMarkLipschitzConstantsOn E K kin g := by
  obtain ⟨Lk, ck, hck⟩ := hreadk
  obtain ⟨Lg, cg, hcg⟩ := hreadg
  refine hasMarkLipschitzConstantsOn_of_eqOn_affine_quadratic_readouts hK hne hconv
    A B Lk Lg ck cg ?_ ?_
  · intro z hz
    rw [hkin z hz, hck z hz]
  · intro z hz
    rw [hg z hz, hcg z hz]

end OTSelector.Reconstruction