import YM.WilsonMS.Scales.StrongPose
/-!
# Grading projections and exponential clock on genuine Wilson-MS fields

Use `ShellSector`, not a monomial or off-shell graded approximation.
At this point grammar `Grade` refers to ENGINEERING weight, not slot count
(which also had to be carefully controlled at the regulating stage).
Projection maps will isolate exactly the diagonal from a filtering system.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1 Lattice
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X C constantCoeff)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k i j : ℕ}
local notation "BΨ" => Ensure.deck G

abbrev Pay (d : ℕ) :=
  Fin (d + 1)

def tileK (G : Gauge) (d : ℕ) (v : Pay d) : FieldEnd G d :=
  Normalize.en (Nat.le_of_lt_succ v.isLt) ∘ₗ part d v.val

lemma tileD (v w : Pay d) (x : Sec G d) :
    tileK G d w (tileK G d v x) = if v = w then tileK G d v x else 0 := by
  rcases eq_or_ne v w with rfl | ht
  · rw [tileK, LinearMap.comp_apply, LinearMap.comp_apply, part_same, if_pos rfl]
  simp_rw [tileK, LinearMap.comp_apply, if_neg ht, part_other _ (fun h => ht (Fin.ext h.symm)),
    map_zero]

lemma whole (p : Sec G d) : ∑ i, tileK G d i p = p :=
  enfits p

lemma tile_ori (p : Sec G d) (i : Pay d) (s : Ortho) :
    tileK G d i (ori s d p) = ori s d (tileK G d i p) :=
  Subtype.ext (part_ori ..)

lemma tile_reel (p : Sec G d) (i : Pay d) : tileK G d i (reel d p) = reel d (tileK G d i p) :=
  Subtype.ext (part_reel ..)

lemma tile_en (v : On.Grade G k) (hk : k ≤ d) (i : Pay d) :
    tileK G d i (en hk v) = if k = i.val then en hk v else 0 := by
  rcases i with ⟨i, hi⟩
  rcases eq_or_ne k i with rfl | he
  · rw [tileK, LinearMap.comp_apply, part_same, if_pos rfl]
  rw [tileK, LinearMap.comp_apply, part_other _ (Ne.symm he), if_neg he, map_zero]

lemma tile_g (i : Glyph BΨ d) (v : Pay d) :
    tileK G d v (glow i) = if i.size = v.val then glow i else 0 := by
  obtain ⟨x, y⟩ := i
  exact tile_en (Ensure.full y) (Nat.le_of_lt_succ x.isLt) _

lemma tile_key (v : Pay d) (x : Sec G d) : (tileK G d v x).val ∈ shellSector G v.val :=
  (part d v.val x).property.1

lemma tile_earlier (v : Pay d) (hh : i ≤ d) (p : Sec G d) (ht : p.val ∈ shellSector G i) :
    (tileK G d v p).val ∈ shellSector G i := by
  by_cases hv : v.val ≤ i
  · exact chain hv (tile_key ..)
  let x : Sec G i := ⟨p.val, ht⟩
  have he : tileK G d v p = 0 := by
    change en (Nat.le_of_lt_succ v.isLt) (part d _ (up hh x)) = 0
    rw [part_up, part_zero (lt_of_not_ge hv) x, map_zero]
  rw [he]
  exact Submodule.zero_mem _

lemma tile_day (v : Pay d) (p : Sec G d) (h : i < v.val) (hi : i ≤ d) (hp : p.val ∈ shellSector G i) :
    tileK G d v p = 0 := by
  let q : Sec G i := ⟨p.val, hp⟩
  change en (Nat.le_of_lt_succ v.isLt) (part d _ (up hi q)) = 0
  rw [part_up, part_zero h q, map_zero]

lemma tile_leaf (v : Pay d) : tileK G d v (leaf G d) = if v.val = 0 then (leaf G d) else 0 := by
  let P : On.Grade G 0 := ⟨1, (leaf G 0).property, MvPolynomial.isWeightedHomogeneous_one ..⟩
  rw [show leaf G d = en (Nat.zero_le d) P from rfl, tile_en]
  simp [eq_comm]

lemma units_tile (p : Sec G d) (v : Pay d) : ((tileK G d v).comp (tileK G d v)) p = tileK G d v p :=
  by rw [LinearMap.comp_apply, tileD, if_pos rfl]
section bill
variable {T U : FieldEnd G d}

def shadows (T : FieldEnd G d) :=
  ∑ i : Pay d, tileK G d i ∘ₗ T ∘ₗ tileK G d i

lemma levy (x : Sec G d) : shadows T x = ∑ i : Pay d, tileK G d i (T (tileK G d i x)) :=
  LinearMap.sum_apply ..

lemma tileskip (i : Pay d) (x : Sec G d) :
    shadows T (tileK G d i x) = tileK G d i (T (tileK G d i x)) := by
  rw [levy, Finset.sum_eq_single i]
  · rw [tileD, if_pos rfl]
  · intro b _ hb
    rw [tileD, if_neg (Ne.symm hb), map_zero, map_zero]
  simp

lemma tile_put (i : Pay d) (x : Sec G d) :
    tileK G d i (shadows T x) = tileK G d i (T (tileK G d i x)) := by
  rw [levy, map_sum]
  simp [tileD]

lemma tile_one (d : ℕ) : shadows (1 : FieldEnd G d) = 1 := by
  apply LinearMap.ext
  intro x
  rw [levy]
  simpa only [Module.End.one_apply, tileD, if_true] using! whole x

lemma tile_zero (G : Gauge) (d : ℕ) : shadows (0 : FieldEnd G d) = 0 := by
  apply LinearMap.ext
  intro x
  simp [levy]

lemma tile_sum (T U : FieldEnd G d) : shadows (T + U) = shadows T + shadows U := by
  ext1 x
  rw [levy, LinearMap.add_apply (shadows T), levy, levy]
  simp_rw [LinearMap.add_apply, map_add, Finset.sum_add_distrib]

lemma tile_total {X : Type} (S : Finset X) (F : X → FieldEnd G d) :
    shadows (∑ i ∈ S, F i) = ∑ i ∈ S, shadows (F i) := by
  induction S using Finset.induction_on with
  | empty => simp [tile_zero G d]
  | insert i s hi ih => rw [Finset.sum_insert hi, tile_sum, ih, Finset.sum_insert hi]

abbrev Flat (W : FieldEnd G d) : Prop :=
  shadows W = W

lemma Flat.freedom (B : FieldEnd G d) : Flat (shadows B) := by
  unfold Flat
  apply LinearMap.ext
  intro x
  rw [levy]
  simp_rw [tileskip, tileD]
  simp only [if_true]
  exact (levy x).symm

lemma tile_change (x : Change G d) : shadows x.val ∈ Change G d := by
  rw [may_change]
  simp_rw [levy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro i _
    rw [tile_leaf]
    split_ifs
    rw [x.property.1, map_zero]
    rw [map_zero, map_zero]
  · intro j hj p hp
    rw [Submodule.coe_sum]
    exact
      Submodule.sum_mem _ fun i _ =>
        tile_earlier i hj _ (x.property.2.1 j hj _ (tile_earlier i hj _ hp))
  · intro p
    rw [map_sum]
    simp_rw [tile_reel, x.property.2.2.1, tile_reel]
  intro s p
  rw [map_sum]
  simp_rw [tile_ori, x.property.2.2.2, tile_ori]

def Tier (X : FieldEnd G d) :=
  ∀ (i j : Pay d), i < j → ∀ x, tileK G d j (X (tileK G d i x)) = 0

lemma tier_change (X : Change G d) : Tier X.val := fun i j h x =>
  tile_day j _ h (Nat.le_of_lt_succ i.isLt)
    (X.property.2.1 _ (Nat.le_of_lt_succ i.isLt) _ (tile_key i x))

lemma tierFlat (hx : Flat T) : Tier T := by
  intro i j hp x
  rw [← show shadows T = T from hx, tileskip, tileD, if_neg hp.ne]

lemma mul_diag (h : Tier T) (hp : Tier U) : shadows (T * U) = shadows T * shadows U := by
  ext1 x
  suffices he : ∀ i : Pay d, shadows (T * U) (tileK G d i x) = shadows T (shadows U (tileK G d i x))
    by
    conv => lhs; rw [← whole x, map_sum]
    rw [Module.End.mul_apply]
    conv_rhs => rw [← whole x, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he i
  intro i
  simp_rw [tileskip, Module.End.mul_apply]
  let y := U (tileK G d i x)
  change tileK G d i (T y) = tileK G d i (T (tileK G d i y))
  conv_lhs => rw [← whole y, map_sum, map_sum]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  intro k _ hk
  rcases lt_or_gt_of_ne hk with he | he
  exact h k i he y
  unfold y
  rw [hp i k he x, map_zero, map_zero]

lemma Flat.product (hT : Flat T) (hU : Flat U) : Flat (T * U) := by
  unfold Flat
  rw [mul_diag (tierFlat hT) (tierFlat hU), hT, hU]
end bill
section Log

variable {x y : ℝ}

abbrev tag (t : ℝ) (d : ℕ) : ℝ :=
  exp ((d : ℝ) * (-t))

lemma tag_add (d : ℕ) : tag x d * tag y d = tag (x + y) d := by
  unfold tag
  rw [← exp_add]
  congr 1
  ring

def window (G : Gauge) (d : ℕ) (t : ℝ) : FieldEnd G d :=
  ∑ i : Pay d, (tag t i.val) • tileK G d i

lemma road (x : ℝ) (p : Sec G d) : window G d x p = ∑ i : Pay d, tag x i.val • tileK G d i p := by
  unfold window
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

lemma pane (t : ℝ) (p : Sec G d) (i : Pay d) :
    window G d t (tileK G d i p) = tag t i.val • tileK G d i p := by
  rw [road, Finset.sum_eq_single_of_mem i (Finset.mem_univ _), tileD, if_pos rfl]
  intro b _ hb
  rw [tileD, if_neg (Ne.symm hb), smul_zero]

lemma pane_g (t : ℝ) (i : Glyph BΨ d) : window G d t (glow i) = tag t i.size • glow i := by
  have he := pane t (glow i) i.1
  rwa [tile_g, if_pos rfl] at he

lemma window0 : window G d 0 = 1 := by
  apply LinearMap.ext
  intro x
  rw [road]
  simp [tag, whole]

lemma tower (G : Gauge) (d : ℕ) (t u : ℝ) : window G d t * window G d u = window G d (t + u) := by
  apply LinearMap.ext
  intro x
  have ht (i : Pay d) :
    (window G d t * window G d u) (tileK G d i x) = window G d (t + u) (tileK G d i x) := by
    rw [Module.End.mul_apply, pane, pane (t + u),
      show ∀ p a, window G d t (a • p) = a • window G d t p from fun p (a : ℝ) =>
        map_smul ((window G d t).restrictScalars ℝ) a p,
      pane, smul_smul, mul_comm, tag_add]
  rw [← whole x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => ht i

lemma leaf_free (t : ℝ) : window G d t (leaf G d) = leaf G d := by
  rw [road]
  simp_rw [tile_leaf]
  rw [Finset.sum_eq_single (⟨0, Nat.zero_lt_succ d⟩ : Pay d)]
  · simp [tag]
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h)), smul_zero]
  simp

lemma window_cap (t : ℝ) (p : Sec G d) (h : i ≤ d) (hv : p.val ∈ shellSector G i) :
    (window G d t p).val ∈ shellSector G i := by
  rw [road, Submodule.coe_sum]
  exact
    Submodule.sum_mem _ fun j _ =>
      ((shellSector G i).restrictScalars ℝ).smul_mem _ (tile_earlier j h p hv)

lemma window_or (s : Signed) (t : ℝ) (p : Sec G d) :
    window G d t (ori s.ortho d p) = ori s.ortho d (window G d t p) := by
  rw [road, road, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tile_ori]
  exact (map_smul ((ori s.ortho d).restrictScalars ℝ) _ _).symm

lemma window_reel (t : ℝ) (p : Sec G d) : reel d (window G d t p) = window G d t (reel d p) := by
  rw [road, road, map_sum]
  simp_rw [reel_scale, tile_reel]

lemma win_hold (t : ℝ) : window G d t - 1 ∈ Change G d := by
  rw [may_change]
  simp_rw [LinearMap.sub_apply, Module.End.one_apply]
  refine ⟨sub_eq_zero.mpr (leaf_free t), ?_, ?_, ?_⟩
  · intro i hi p hp
    exact Submodule.sub_mem _ (window_cap t p hi hp) hp
  · intro p
    rw [map_sub, window_reel]
  intro s p
  rw [map_sub, window_or]
end Log
end YM.WilsonMS.GFlow
