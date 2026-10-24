import OTSelector.Finite.MaxCardValueStability
import OTSelector.Probability.MarkedTileModel
import OTSelector.Probability.MarkedBlockValueIntegral

/-!
# The leaf-block value of one tile

The tile-selecting model of `MarkedTileModel` encodes a finite family of local
models in one marked cloud: the mark space is `C × A`, and the first coordinate
of the mark selects the tile.  This module isolates one tile `c` of such a cloud
and proves that the maximum-cardinality value of the ambient tile block indexed
by `c` equals the marked tilted value of the local cloud of points whose label
is `c`.

The identification has two ingredients:

* reindexing the ambient block matrix, enumerated by `blockEmbeddingS` and
  `blockEmbeddingT`, along the increasing enumeration of the label cloud;
* the entrywise identity for two points of the same tile: the ambient kinetic
  coefficient `r ^ (2/q)` together with the kernel scaling by `w c ^ (1/q)`
  equals the local coefficient `(r * w c) ^ (2/q)`.
-/

open scoped NNReal BigOperators

noncomputable section
namespace OTSelector.Probability

/-- The indices of a marked sequence whose mark label equals `c`. -/
noncomputable def labelFilter {q : ℕ} {C A : Type*} [DecidableEq C] (c : C)
    (z : MarkedCloudSpace q (C × A)) : Finset (Fin z.1) :=
  Finset.univ.filter (fun i : Fin z.1 => (z.2 i).2.1 = c)

/-- The subcloud of an infinite marked sequence whose mark label equals `c`,
in increasing index order.  The sequence is padded outside the selected indices
with a fixed point of the ambient sequence, so the cloud remains total. -/
noncomputable def labelCloud {q : ℕ} {C A : Type*} [DecidableEq C] (c : C)
    (z : MarkedCloudSpace q (C × A)) : MarkedCloudSpace q A :=
  ⟨(labelFilter c z).card, fun j : ℕ =>
    if h : j < (labelFilter c z).card then
      ((z.2 ((labelFilter c z).orderIsoOfFin rfl ⟨j, h⟩).1).1,
       (z.2 ((labelFilter c z).orderIsoOfFin rfl ⟨j, h⟩).1).2.2)
    else ((z.2 0).1, (z.2 0).2.2)⟩

/-- The number of points of `labelCloud c z` is the number of indices whose
mark label is `c`. -/
theorem labelCloud_fst {q : ℕ} {C A : Type*} [DecidableEq C] (c : C)
    (z : MarkedCloudSpace q (C × A)) :
    (labelCloud c z).1 = (labelFilter c z).card := rfl

/-- The value of `orderIsoOfFin` as an element of the ambient type does not
depend on the target cardinality, only on the index value. -/
theorem orderIsoOfFin_val_eq {α : Type*} [LinearOrder α] {s : Finset α}
    {k k' : ℕ} (h : s.card = k) (h' : s.card = k') {i : Fin k} {i' : Fin k'}
    (hii : (i : ℕ) = (i' : ℕ)) :
    ((s.orderIsoOfFin h i).1 : α) = ((s.orderIsoOfFin h' i').1 : α) := by
  subst h
  subst h'
  rw [Fin.ext hii]

/-- The `j`-th point of `labelCloud c z` is the point and the local mark of the
`j`-th index (in increasing order) whose label is `c`. -/
theorem labelCloud_apply {q : ℕ} {C A : Type*} [DecidableEq C] (c : C)
    (z : MarkedCloudSpace q (C × A)) (j : Fin (labelCloud c z).1) :
    (labelCloud c z).2 (j : ℕ) =
      ((z.2 ((labelFilter c z).orderIsoOfFin (labelCloud_fst c z).symm j).1).1,
       (z.2 ((labelFilter c z).orderIsoOfFin (labelCloud_fst c z).symm j).1).2.2) := by
  dsimp only [labelCloud]
  have hj : (j : ℕ) < (labelFilter c z).card := by
    rw [← labelCloud_fst c z]
    exact j.isLt
  rw [dif_pos hj]
  have hidx : ((labelFilter c z).orderIsoOfFin rfl ⟨(j : ℕ), hj⟩).1 =
      ((labelFilter c z).orderIsoOfFin (labelCloud_fst c z).symm j).1 :=
    orderIsoOfFin_val_eq rfl (labelCloud_fst c z).symm rfl
  rw [hidx]
  rfl

/-- The global leaf-block value of tile `c`: the maximum-cardinality value of the
submatrix of the ambient tile cost restricted to source and target points whose
mark label is `c`. -/
noncomputable def tileBlockValue {q : ℕ} {C A B : Type*} [DecidableEq C]
    (w : C → ℝ≥0) (kin : C → A → B → (Fin q → ℝ) → ℝ) (g : C → A → B → ℝ)
    (Kcross r t : ℝ) (ω : TwoMarkedCloudSpace q (C × A) (C × B)) (c : C) : ℝ :=
  PartialMatching.maxCardValue
    (blockCost
      (fun i : Fin (mSourceCount ω) => (mSourceMark ω i).1)
      (fun j : Fin (mTargetCount ω) => (mTargetMark ω j).1)
      (fun i j => markedEdgeCost q r (tileKin q w kin Kcross) (tileProbe g) t ω
        (i : ℕ) (j : ℕ)) c)

/-- **The entrywise identity for two points of one tile.**  For a source point
and a target point carrying the same tile label `c`, the ambient edge cost of
the tile model is the local edge cost of tile `c` at intensity `r * w c`. -/
theorem markedEdgeCost_tileKin_eq {q : ℕ} {C A B : Type*} [DecidableEq C]
    {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Kcross r t : ℝ} (_hq : 0 < q) (hr : 0 ≤ r)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (c : C) (ω : TwoMarkedCloudSpace q (C × A) (C × B)) (i j : ℕ)
    (hi : (mSourceMark ω i).1 = c) (hj : (mTargetMark ω j).1 = c) :
    markedEdgeCost q r (tileKin q w kin Kcross) (tileProbe g) t ω i j =
      (r * (w c : ℝ)) ^ (2 / (q : ℝ)) *
          kin c (mSourceMark ω i).2 (mTargetMark ω j).2
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) +
        t * g c (mSourceMark ω i).2 (mTargetMark ω j).2 := by
  unfold markedEdgeCost mKineticCost mProbe tileKin tileProbe
  have hcd : (mSourceMark ω i).1 = (mTargetMark ω j).1 := hi.trans hj.symm
  rw [if_pos hcd, if_pos hcd]
  rw [hi]
  have hw0 : (0 : ℝ) ≤ (w c : ℝ) := by positivity
  have hs0 : (0 : ℝ) ≤ (w c : ℝ) ^ (1 / (q : ℝ)) := Real.rpow_nonneg hw0 _
  rw [hkin_homog c (mSourceMark ω i).2 (mTargetMark ω j).2
    ((w c : ℝ) ^ (1 / (q : ℝ))) hs0
    (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))]
  have hcoef : r ^ (2 / (q : ℝ)) * ((w c : ℝ) ^ (1 / (q : ℝ))) ^ 2 =
      (r * (w c : ℝ)) ^ (2 / (q : ℝ)) := by
    have hw2 : ((w c : ℝ) ^ (1 / (q : ℝ))) ^ 2 = (w c : ℝ) ^ (2 / (q : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0]
      congr 1
      ring
    rw [hw2, ← Real.mul_rpow hr hw0]
  rw [← mul_assoc, hcoef]

set_option maxHeartbeats 1600000 in
/-- **One tile, one local model.**  The ambient block value of the tile `c` is
the marked tilted value of the label cloud of `c` at intensity `r * w c`. -/
theorem tileBlockValue_eq
    {q : ℕ} {C A B : Type*} [DecidableEq C] [Fintype C]
    {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Kcross r t : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (ω : TwoMarkedCloudSpace q (C × A) (C × B)) (c : C) :
    tileBlockValue w kin g Kcross r t ω c =
      markedTilted q (r * (w c : ℝ)) (kin c) (g c) t
        (labelCloud c ω.1, labelCloud c ω.2) := by
  classical
  let labS : Fin (mSourceCount ω) → C := fun i => (mSourceMark ω i).1
  let labT : Fin (mTargetCount ω) → C := fun j => (mTargetMark ω j).1
  let edge : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => markedEdgeCost q r (tileKin q w kin Kcross) (tileProbe g) t ω (i : ℕ) (j : ℕ)
  have hsizeS : blockSizeS labS c = (labelCloud c ω.1).1 := rfl
  have hsizeT : blockSizeT labT c = (labelCloud c ω.2).1 := rfl
  have hfinS : blockFinset labS c = labelFilter c ω.1 := rfl
  have hfinT : blockFinset labT c = labelFilter c ω.2 := rfl
  have hmemS : ∀ p, blockEmbeddingS labS c p ∈ labelFilter c ω.1 := by
    intro p
    rw [← hfinS]
    exact blockEmbeddingS_mem labS c p
  have hmemT : ∀ p, blockEmbeddingT labT c p ∈ labelFilter c ω.2 := by
    intro p
    rw [← hfinT]
    exact blockEmbeddingT_mem labT c p
  -- The permutation relating the block enumeration `blockEmbeddingS` with the
  -- increasing enumeration of the label cloud.
  let eFunS : Fin (blockSizeS labS c) → Fin (labelCloud c ω.1).1 := fun p =>
    (labelFilter c ω.1).orderIsoOfFin (labelCloud_fst c ω.1).symm |>.symm
      ⟨blockEmbeddingS labS c p, hmemS p⟩
  let eFunT : Fin (blockSizeT labT c) → Fin (labelCloud c ω.2).1 := fun p =>
    (labelFilter c ω.2).orderIsoOfFin (labelCloud_fst c ω.2).symm |>.symm
      ⟨blockEmbeddingT labT c p, hmemT p⟩
  have hePropS : ∀ p, (labelFilter c ω.1).orderIsoOfFin (labelCloud_fst c ω.1).symm (eFunS p) =
      ⟨blockEmbeddingS labS c p, hmemS p⟩ := by
    intro p
    exact (labelFilter c ω.1).orderIsoOfFin (labelCloud_fst c ω.1).symm |>.apply_symm_apply _
  have hePropT : ∀ p, (labelFilter c ω.2).orderIsoOfFin (labelCloud_fst c ω.2).symm (eFunT p) =
      ⟨blockEmbeddingT labT c p, hmemT p⟩ := by
    intro p
    exact (labelFilter c ω.2).orderIsoOfFin (labelCloud_fst c ω.2).symm |>.apply_symm_apply _
  have heInjS : Function.Injective eFunS := by
    intro p q' hpq
    apply blockEmbeddingS_injective labS c
    have h1 := congrArg (fun j =>
      ((labelFilter c ω.1).orderIsoOfFin (labelCloud_fst c ω.1).symm j).1) hpq
    rw [hePropS p, hePropS q'] at h1
    exact h1
  have heInjT : Function.Injective eFunT := by
    intro p q' hpq
    apply blockEmbeddingT_injective labT c
    have h1 := congrArg (fun j =>
      ((labelFilter c ω.2).orderIsoOfFin (labelCloud_fst c ω.2).symm j).1) hpq
    rw [hePropT p, hePropT q'] at h1
    exact h1
  let eS : Fin (blockSizeS labS c) ≃ Fin (labelCloud c ω.1).1 :=
    Equiv.ofBijective eFunS
      (Fintype.bijective_iff_injective_and_card eFunS |>.mpr
        ⟨heInjS, by
          rw [Fintype.card_fin, Fintype.card_fin]
          exact hsizeS⟩)
  let eT : Fin (blockSizeT labT c) ≃ Fin (labelCloud c ω.2).1 :=
    Equiv.ofBijective eFunT
      (Fintype.bijective_iff_injective_and_card eFunT |>.mpr
        ⟨heInjT, by
          rw [Fintype.card_fin, Fintype.card_fin]
          exact hsizeT⟩)
  have heS_apply : ∀ p, eS p = eFunS p := fun p => rfl
  have heT_apply : ∀ p, eT p = eFunT p := fun p => rfl
  have hiS : ∀ p, ((labelFilter c ω.1).orderIsoOfFin
      (labelCloud_fst c ω.1).symm (eS p)).1 =
      blockEmbeddingS labS c p := by
    intro p
    rw [heS_apply p]
    exact congrArg Subtype.val (hePropS p)
  have hiT : ∀ p, ((labelFilter c ω.2).orderIsoOfFin
      (labelCloud_fst c ω.2).symm (eT p)).1 =
      blockEmbeddingT labT c p := by
    intro p
    rw [heT_apply p]
    exact congrArg Subtype.val (hePropT p)
  -- The local points of the label cloud are the ambient points of the block.
  have hpointS : ∀ p : Fin (blockSizeS labS c),
      (labelCloud c ω.1).2 (eS p) =
        (mSourcePoint ω ↑(blockEmbeddingS labS c p),
         (mSourceMark ω ↑(blockEmbeddingS labS c p)).2) := by
    intro p
    rw [labelCloud_apply c ω.1 (eS p), hiS p]
    rfl
  have hpointT : ∀ p : Fin (blockSizeT labT c),
      (labelCloud c ω.2).2 (eT p) =
        (mTargetPoint ω ↑(blockEmbeddingT labT c p),
         (mTargetMark ω ↑(blockEmbeddingT labT c p)).2) := by
    intro p
    rw [labelCloud_apply c ω.2 (eT p), hiT p]
    rfl
  have hpointS_fst : ∀ p : Fin (blockSizeS labS c),
      ((labelCloud c ω.1).2 (eS p)).1 =
        mSourcePoint ω ↑(blockEmbeddingS labS c p) := by
    intro p
    rw [hpointS p]
  have hpointS_snd : ∀ p : Fin (blockSizeS labS c),
      ((labelCloud c ω.1).2 (eS p)).2 =
        (mSourceMark ω ↑(blockEmbeddingS labS c p)).2 := by
    intro p
    rw [hpointS p]
  have hpointT_fst : ∀ p : Fin (blockSizeT labT c),
      ((labelCloud c ω.2).2 (eT p)).1 =
        mTargetPoint ω ↑(blockEmbeddingT labT c p) := by
    intro p
    rw [hpointT p]
  have hpointT_snd : ∀ p : Fin (blockSizeT labT c),
      ((labelCloud c ω.2).2 (eT p)).2 =
        (mTargetMark ω ↑(blockEmbeddingT labT c p)).2 := by
    intro p
    rw [hpointT p]
  -- The selected indices are exactly the points whose label is `c`.
  have hpredS : ∀ p : Fin (blockSizeS labS c),
      (mSourceMark ω ↑(blockEmbeddingS labS c p)).1 = c := by
    intro p
    have hmem := blockEmbeddingS_mem labS c p
    simpa only [labS] using (mem_blockFinset.mp hmem)
  have hpredT : ∀ p : Fin (blockSizeT labT c),
      (mTargetMark ω ↑(blockEmbeddingT labT c p)).1 = c := by
    intro p
    have hmem := blockEmbeddingT_mem labT c p
    simpa only [labT] using (mem_blockFinset.mp hmem)
  -- The local matrix indexed by the increasing enumeration of the label cloud.
  let L : Fin (labelCloud c ω.1).1 → Fin (labelCloud c ω.2).1 → ℝ := fun p q' =>
    (r * (w c : ℝ)) ^ (2 / (q : ℝ)) *
        kin c ((labelCloud c ω.1).2 p).2
            ((labelCloud c ω.2).2 q').2
          (mDisplacement ((labelCloud c ω.1).2 p).1
            ((labelCloud c ω.2).2 q').1) +
      t * g c ((labelCloud c ω.1).2 p).2
            ((labelCloud c ω.2).2 q').2
  -- The entrywise identity.
  have hentry : ∀ (p : Fin (blockSizeS labS c)) (q' : Fin (blockSizeT labT c)),
      edge (blockEmbeddingS labS c p) (blockEmbeddingT labT c q') = L (eS p) (eT q') := by
    intro p q'
    have hedge := markedEdgeCost_tileKin_eq (q := q) (C := C) (A := A) (B := B)
      (w := w) (kin := kin) (g := g) (Kcross := Kcross) (r := r) (t := t)
      hq hr hkin_homog c ω ↑(blockEmbeddingS labS c p) ↑(blockEmbeddingT labT c q')
      (hpredS p) (hpredT q')
    have hL : L (eS p) (eT q') =
        (r * (w c : ℝ)) ^ (2 / (q : ℝ)) *
            kin c (mSourceMark ω ↑(blockEmbeddingS labS c p)).2
                (mTargetMark ω ↑(blockEmbeddingT labT c q')).2
              (mDisplacement (mSourcePoint ω ↑(blockEmbeddingS labS c p))
                (mTargetPoint ω ↑(blockEmbeddingT labT c q'))) +
          t * g c (mSourceMark ω ↑(blockEmbeddingS labS c p)).2
                (mTargetMark ω ↑(blockEmbeddingT labT c q')).2 := by
      dsimp only [L]
      rw [hpointS_fst p, hpointS_snd p, hpointT_fst q', hpointT_snd q']
    dsimp only [edge]
    rw [hedge]
    exact hL.symm
  -- The block matrix is a reindexing of the local matrix.
  have hcost : blockCost labS labT edge c = fun p => fun q' => L (eS p) (eT q') := by
    funext p q'
    exact hentry p q'
  have hmax : PartialMatching.maxCardValue (blockCost labS labT edge c) =
      PartialMatching.maxCardValue L := by
    rw [hcost]
    have hre := PartialMatching.maxCardValue_reindex (c := L) (e := eS.symm) (f := eT.symm)
    simpa only [Equiv.symm_symm] using hre
  show PartialMatching.maxCardValue (blockCost labS labT edge c) =
      markedTilted q (r * (w c : ℝ)) (kin c) (g c) t
        (labelCloud c ω.1, labelCloud c ω.2)
  rw [hmax]
  unfold markedTilted tiltedCloudValue
  rfl

end OTSelector.Probability
