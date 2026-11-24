import YM.Comparison.RG02.Algebra.Markers
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coupling order & marker-mode coefficients

Encode jets in one ordinary expansion parameter (`g=beta^{-1/2}` later)
through cut `r`. Uses `r` extra polar marks (generate `g` by their sum),
independent of source-marker prohibitions. All occurrences of `PowerSeries`
in this development are FORMAL: evaluation/cost always specifies a cut.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02
namespace Polar

open Marker Extra.Trajectories Primitives.GCC.Anchor Multi
open Finset Sum Function PowerSeries
open scoped BigOperators

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Combined g and source modes. -/
def ledger (r : ℕ) (R : Census V) : Census (Fin r ⊕ V) where
  choices := Finset.univ.filter fun s => s.toRight ∈ R.choices
  blank := by
    simp only [mem_filter, mem_univ, true_and]
    exact R.blank
  solo x := by
    rcases x with x|x
    · simp only [mem_filter,mem_univ,true_and]
      rw [show ({inl x} : Finset (Fin r ⊕ V)).toRight = ∅ by ext; simp]
      exact R.blank
    · simp only [mem_filter,mem_univ,true_and]
      rw [show ({inr x} : Finset (Fin r ⊕ V)).toRight = {x} by ext; simp]
      exact R.solo _
  down h _ h' := mem_filter.mpr ⟨mem_univ _, R.down ((mem_filter.mp h).2) _ (toRight_subset_toRight h')⟩

variable {r : ℕ} {R : Census V}

def joint (A : Finset (Fin r)) (T : R.Mode) : (ledger r R).Mode :=
    ⟨A.disjSum T.val, mem_filter.mpr ⟨mem_univ _, by rw [toRight_disjSum]; exact T.property⟩⟩

def srcPart (w : (ledger r R).Mode) : R.Mode :=
    ⟨(w.val : Finset (Fin r ⊕ V)).toRight,(mem_filter.mp w.property).2⟩

theorem pieces (w : (ledger r R).Mode) : joint w.val.toLeft (srcPart w)=w :=
    Subtype.ext Finset.toLeft_disjSum_toRight

@[simp] theorem src_joint (A : Finset (Fin r)) (T : R.Mode) : srcPart (joint A T) = T := by
  apply Subtype.ext; simp [joint,srcPart]

@[simp] theorem powPart_joint (A : Finset (Fin r)) (T : R.Mode) : (joint A T).val.toLeft = A :=
   Finset.toLeft_disjSum

@[simp] theorem joint_nil : joint ∅ R.quiet = (ledger r R).quiet := by
   apply Subtype.ext; ext x; cases x <;> simp [joint,Census.quiet]


private def keepLinear (r : ℕ) (R : Census V) : Poly R →ₗ[ℂ] Poly (ledger r R) where
  toFun p := ∑ t, Poly.send (joint ∅ t) (p.part t)
  map_add' p q := by
    simp only [Poly.part_plus, Extra.Trajectories.send_add, Finset.sum_add_distrib]
  map_smul' a p := by simp only [Poly.part_smul, Multi.send_scale, Finset.smul_sum, RingHom.id_apply]

private theorem keepLinear_single (T : R.Mode) (x : ℂ) :
    keepLinear r R (Poly.send T x) = Poly.send (joint ∅ T) x := by
  change (∑ t, Poly.send (R:=ledger r R) (joint ∅ t) ((Poly.send T x).part t)) = _
  rw [sum_eq_single_of_mem T (mem_univ _)]
  · rw [Poly.part_send, if_pos rfl]
  intro i _ hi
  rw [Poly.part_send, if_neg hi, Poly.send_zero]

private theorem inject_merge (a b c : R.Mode) :
    Poly.merges (R:=ledger r R) (joint ∅ a) (joint ∅ b) (joint ∅ c) ↔ Poly.merges a b c := by
  unfold Poly.merges joint; dsimp only
  constructor
  · rintro ⟨hd,h⟩
    refine ⟨disjoint_left.mpr (fun v hv hj => ?_), ?_⟩
    · exact disjoint_left.mp hd (inr_mem_disjSum.mpr hv) (inr_mem_disjSum.mpr hj)
    · simpa only [toRight_union, toRight_disjSum] using congrArg toRight h
  · rintro ⟨hd,h⟩
    refine ⟨disjoint_left.mpr ?_,by ext x; cases x <;> simp [← h]⟩
    rintro (x|x) hx hy
    · simpa using! (show False from notMem_empty _ (inl_mem_disjSum.mp hx))
    exact disjoint_left.mp hd (inr_mem_disjSum.mp hx) (inr_mem_disjSum.mp hy)

def keep (r : ℕ) (R : Census V) : Poly R →ₐ[ℂ] Poly (ledger r R) := by
  refine AlgHom.ofLinearMap (keepLinear r R) ?_ ?_
  · change keepLinear r R (Poly.send R.quiet 1) = _
    rw [keepLinear_single, joint_nil]; rfl
  · have individual (a b : R.Mode) (x y : ℂ) : keepLinear r R (Poly.send a x * Poly.send b y)=
        keepLinear r R (Poly.send a x) * keepLinear r R (Poly.send b y) := by
      rw [keepLinear_single, keepLinear_single]
      by_cases H : ∃ t,Poly.merges a b t
      · obtain ⟨t,hT⟩:=H
        rw [send_prod hT, keepLinear_single, send_prod ((inject_merge (r:=r) a b t).mpr hT)]
      have he : ¬ ∃ w : (ledger r R).Mode, Poly.merges (joint ∅ a) (joint ∅ b) w := by
        rintro ⟨w,hw⟩
        have hLeft : w.val.toLeft=∅ := by rw [← hw.2, toLeft_union]; simp only [powPart_joint, union_self]
        apply H; refine ⟨srcPart w,(inject_merge (r:=r) ..).mp ?_⟩
        rw [show joint ∅ (srcPart w) = w from (hLeft ▸ pieces w)]; exact hw
      rw [send_noProd H, send_noProd he, map_zero]
    intro x y
    rw [← Poly.studs x, ← Poly.studs y]
    simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum,individual,Finset.sum_mul,Finset.mul_sum]

theorem keep_single (T : R.Mode) (x : ℂ) :
    keep r R (Poly.send T x) = Poly.send (joint ∅ T) x := keepLinear_single ..

theorem joint_subset (A B : Finset (Fin r)) (T U : R.Mode) :
    (joint A T).val ⊆ (joint B U).val ↔ A ⊆ B ∧ T.val ⊆ U.val := by
  simp only [joint,disjSum_subset,toLeft_disjSum,toRight_disjSum]

theorem joint_sdiff (A B : Finset (Fin r)) (T U : R.Mode) :
    diff (joint A T) (joint B U).val = joint (A \ B) (diff T U.val) := by
  apply Subtype.ext
  ext x
  cases x <;> simp [joint,diff]

/-- The formal coupling variable as a sum of indistinguishable-in-calculation but
*distinct-in-expansion* markers. -/
def variableG (r : ℕ) (R : Census V) :=
  lambda (ledger r R) (Sum.elim (fun _ => 1) (fun _ => 0))

theorem g_pow_part (A : Finset (Fin r)) (T : R.Mode) (k : ℕ) :
    ((variableG r R)^k).part (joint A T) = if T=R.quiet ∧ A.card=k then (k.factorial:ℂ) else 0 := by
  rw [variableG, lambda_pow_part]
  by_cases hT : T=R.quiet
  · subst T
    have ht : ∀ s∈(joint A R.quiet).val, (Sum.elim (fun _ : Fin r => (1:ℂ)) (fun _ : V => 0)) s=1 := by
      rintro (x|x) h
      · rfl
      simp [joint,Census.quiet] at h
    rw [Finset.prod_eq_one ht]
    simp only [joint, card_disjSum,Census.quiet,card_empty,add_zero,mul_one,true_and]
  have ht : T.val.Nonempty := not_imp_not.mpr (fun e : ¬ T.val.Nonempty =>
    Subtype.ext (not_nonempty_iff_eq_empty.mp e)) hT |> Classical.not_not.mp
  obtain ⟨i,hi⟩:=ht
  have he : inr i ∈ (joint A T).val := inr_mem_disjSum.mpr hi
  rw [Finset.prod_eq_zero he (show Sum.elim (fun _ : Fin r => (1:ℂ)) (fun _ : V => 0) (inr i) = 0 from rfl)]
  simp only [hT,false_and,if_false,mul_zero,ite_self]

theorem g_pow_high {k : ℕ} (h : r < k) : (variableG r R)^k=0 := by
  ext w
  rw [← pieces w, g_pow_part, if_neg]
  · rfl
  intro H
  rw [← H.2] at h
  have he := Finset.card_le_univ w.val.toLeft
  simp only [Fintype.card_fin] at he; omega

theorem monomial_read (x : Poly R) (k : ℕ) (A : Finset (Fin r)) (T : R.Mode) :
    (keep r R x * (variableG r R)^k).part (joint A T) =
      if A.card=k then (k.factorial:ℂ)*x.part T else 0 := by
  nth_rw 1 [← Poly.studs x]
  rw [map_sum, Finset.sum_mul, Poly.part_sum]
  rw [sum_eq_single_of_mem T (mem_univ _)]
  · rw [keep_single, mul_at_part, if_pos ((joint_subset ..).2 ⟨empty_subset _,subset_refl _⟩),
      joint_sdiff, g_pow_part, show diff T T.val = R.quiet from Subtype.ext (by simp [diff,Census.quiet])]
    simp only [true_and,sdiff_empty]; split <;> simp [mul_comm]
  intro b hb h
  rw [keep_single, mul_at_part]
  by_cases hB : b.val ⊆ T.val
  · have he : diff T b.val ≠ R.quiet := by
      intro hi
      apply h; apply Subtype.ext; apply Subset.antisymm hB
      exact Finset.sdiff_eq_empty_iff_subset.mp (congr_arg Subtype.val hi)
    rw [if_pos ((joint_subset ..).2 ⟨empty_subset _, hB⟩),joint_sdiff,g_pow_part,
      if_neg (fun H => he H.1),mul_zero]
  rw [if_neg (fun he => hB ((joint_subset ..).1 he).2)]

-- Truncated substitution without topology obligations.
def spread (r : ℕ) (x : PowerSeries (Poly R)) : Poly (ledger r R) :=
    ∑ i ∈ Finset.range (r+1), keep r R (coeff i x) * (variableG r R)^i

theorem spread_part (A : Finset (Fin r)) (T : R.Mode) (x : PowerSeries (Poly R)) :
    (spread r x).part (joint A T) = (A.card.factorial:ℂ) * (coeff A.card x).part T := by
  rw [spread, Poly.part_sum, sum_eq_single_of_mem A.card (mem_range.mpr ?_)]
  · rw [monomial_read,if_pos rfl]
  · exact fun i _ hi => by rw [monomial_read,if_neg (Ne.symm hi)]
  simpa using Nat.lt_succ_of_le (Finset.card_le_univ A)

end Polar

open Finset PowerSeries
open scoped BigOperators

/-- Cut through `r` inclusive. -/
def sameThrough {A : Type*} [Semiring A] (r : ℕ) (x y : PowerSeries A) :=
   ∀ i ≤ r, coeff i x = coeff i y

/-- Spread tagged powers also provides an overflow formula for one-dimensional evaluation.
We expose the overflow as a separate polynomial: no infinite-series substitution. -/
def through {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (x : PowerSeries A) (r : ℕ) (b : B) : B :=
    ∑ i ∈ Finset.range (r+1), f (coeff i x)*b^i

def overflow {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (x y : PowerSeries A) (r : ℕ) (b : B) : B :=
    ∑ i ∈ (Finset.range (r+1) ×ˢ Finset.range (r+1)).filter (fun i : ℕ × ℕ => ¬ i.1+i.2 ≤ r),
      f (coeff i.1 x)*f (coeff i.2 y)*b^(i.1+i.2-(r+1))

theorem through_product {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (x y : PowerSeries A) (r : ℕ) (b : B) :
    through f x r b * through f y r b = through f (x*y) r b + overflow f x y r b * b^(r+1) := by
  let q (i : ℕ × ℕ) := f (coeff i.1 x)*f (coeff i.2 y)*b^(i.1+i.2)
  let J := Finset.range (r+1)
  let T := J ×ˢ J
  have hm : (∑ i∈T.filter (fun i : ℕ × ℕ => i.1+i.2≤r), q i) =
      through f (x*y) r b := by
    rw [show T.filter (fun i : ℕ × ℕ => i.1+i.2≤r) = J.biUnion Finset.antidiagonal by
      ext ⟨u,v⟩
      simp only [mem_filter,T,J,mem_range, mem_product,mem_biUnion, mem_antidiagonal]
      constructor
      · rintro ⟨⟨hl,hv⟩,h⟩; exact ⟨u+v,by omega,rfl⟩
      rintro ⟨k, hk,h⟩; omega]
    rw [Finset.sum_biUnion]
    · unfold through
      refine sum_congr rfl fun i _ => ?_
      rw [coeff_mul,map_sum,Finset.sum_mul]
      refine sum_congr rfl fun j h => ?_
      dsimp only [q]
      rw [Finset.mem_antidiagonal.mp h, map_mul]
    intro i hi j hj hh
    apply Finset.disjoint_left.mpr
    intro p he he'
    exact hh ((mem_antidiagonal.mp he).symm.trans (mem_antidiagonal.mp he'))
  calc
    _ = ∑ i∈T,q i := by
        simp_rw [through, show T = J ×ˢ J from rfl, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        dsimp only [q]
        rw [pow_add]; ring
    _ = _ := by
      rw [← hm, ← sum_filter_add_sum_filter_not T (fun i : ℕ × ℕ => i.1+i.2≤r), overflow, Finset.sum_mul]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have h := (mem_filter.mp hi).2
      change _ = _*b^_*_
      dsimp only [q]; rw [mul_assoc (_*_) _ (b^(r+1)), ← pow_add, Nat.sub_add_cancel]; omega

namespace Polar
open Marker Function

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {r : ℕ} {R : Census V}

theorem spread_through (x : PowerSeries (Poly R)) :
    spread r x = through (keep r R).toRingHom x r (variableG r R) := rfl

theorem spread_mul (x y : PowerSeries (Poly R)) :
    spread r (x*y) = spread r x * spread r y := by
  rw [spread_through, spread_through, spread_through, through_product,
    g_pow_high (Nat.lt_succ_self r), mul_zero, add_zero]

theorem spread_const (x : Poly R) : spread r (PowerSeries.C x) = keep r R x := by
  unfold spread
  rw [sum_eq_single_of_mem (0 : ℕ) (by simp)]
  · simp
  intro i _ hi
  rw [coeff_C_of_ne_zero hi,map_zero,zero_mul]

def encode (r : ℕ) (R : Census V) : PowerSeries (Poly R) →ₐ[ℂ] Poly (ledger r R) where
  toFun := spread r
  map_add' := by intro x y; simp only [spread,map_add, add_mul,Finset.sum_add_distrib]
  map_zero' := by simp [spread]
  map_one' := by
    rw [show (1 : PowerSeries (Poly R)) = PowerSeries.C (1 : Poly R) from (map_one _).symm,
      spread_const, map_one]
  map_mul' := spread_mul
  commutes' x := by rw [PowerSeries.algebraMap_apply, spread_const, (keep r R).commutes]

theorem encode_part (x : PowerSeries (Poly R)) (A : Finset (Fin r)) (T : R.Mode) :
    (encode r R x).part (joint A T) = (A.card.factorial:ℂ) * (coeff A.card x).part T :=
    spread_part A T x

@[simp] theorem encode_quiet (x : PowerSeries (Poly R)) :
    (encode r R x).part (ledger r R).quiet = (coeff 0 x).part R.quiet := by
  rw [← joint_nil, encode_part]; simp

theorem encode_iff {x y : PowerSeries (Poly R)} :
    encode r R x = encode r R y ↔ sameThrough r x y := by
  constructor
  · intro h i hi
    obtain ⟨A,-, hA⟩ := Finset.exists_subset_card_eq (s:=univ (α:=Fin r)) (by simpa using hi)
    ext T
    have H := congrArg (fun z => Poly.part z (joint A T)) h
    simp_rw [encode_part,hA] at H
    exact mul_left_cancel₀ (show (i.factorial:ℂ)≠0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)) H
  intro h; ext i; rw [← pieces i, encode_part, encode_part,h]
  simpa using card_le_univ i.val.toLeft

end Polar
end YM.Comparison.RG02
