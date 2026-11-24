import YM.FormalOPE.RG10.Routes.Ticked
import YM.FormalOPE.RG10.Routes.Tickets

/-!
# Polynomial moment budgets for a linked cluster, after all branch choices

Spatial uniformity through explicitly requested input norms. Fine-leg
covariance cost here: absolute weighted row, one shared q. No restriction on rank of gauge group or
number of locations for proof, but constants explicitly depend on the given gauges etc via those
input bounds, mark arity and moment order. No physical estimates. Lens bills not radii of
inputs until chosen by geometry. Bulk unmarked vertices use internal diameter and at each charge
must hold an actual input fluctuation leg, never summing freely over vacuum translations at this
scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open MvPolynomial Finset Marker Joins Joins.Gauss Function Fintype
open Primitives.GCC Grove Charge Beams
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {X I J B V : Type} [Fintype J] [DecidableEq I] [Fintype I] [DecidableEq V]
variable {T : Tape X} (p : (I⊕B) → X) (q : I → Row J)
variable {S : Finset V} {o b : V} {f : Parent V} (P : V→Packet (I⊕B))
variable (m : Packet (I⊕B))

def pins (T : Tape X) (n : ℕ) (m : Packet (I⊕B)) (a : I) := ∑ i∈m.support.filter (fun i => a∈pipes i), tip (diam p i T) n*‖coeff i m‖

def schur (T : Tape X) (n : ℕ) (K : ℝ) := ∀ a : I, ∑ b, coinAt p q T n a b ≤ K
omit [DecidableEq I] in
lemma schur_cov {K : ℝ} {n} (h : schur p q T n K) : cov q K := by
  intro a; apply le_trans _ (h a); apply sum_le_sum; intro b _
  exact le_mul_of_one_le_left (crossing_nn ..) (tip_charge (T.sign ..) _)

variable (A E O : Lens T)
local notation "η" => O.m ∘ p ∘ Sum.inr
local notation "w" => radius p A E o b
variable (K : ℝ) (n d : ℕ) (h : schur p q T (n+n) K)
    (hd : ∀ i∈ S, ∀ a∈ (P i).support, rank a≤d)
    (C : V→ℝ) (hk : ∀ i∈ S \ {o}, i≠b → ∀ x, pins p T (n+n) (P i) x ≤ C i)
    (hm : worth (E.m ∘ p) (n+n) (P b) ≤ C b)
    (ht : 1 ≤ K) (hf : Good S {o} f) (ho : o∈S) (hb : b∈S) (hne : b ≠ o) (hc : ∀ i∈S, 0 ≤ C i)

def fieldFee (o b i : V) (a : Index I B) := tip (radius p A E o b i a) (n+n)*‖coeff a (P i)‖
local notation "FF" => fieldFee p P A E n o b
omit [DecidableEq I] [Fintype I] in
lemma field_sign (i : V) (a) : 0 ≤ FF i a := mul_nonneg (tip_pos (radius_nn p A E (fun _=>a) i) _).le (norm_nonneg _)

include hk hm in
omit [Fintype I] in
private lemma also_mark (i : V) (hi : i∈S\{o}) (x : I) :
    ∑ a∈ (P i).support.filter (fun a=> x∈pipes a), FF i a ≤ C i := by
  by_cases hj : i=b
  · subst i
    have hh : b≠o := fun he => (mem_sdiff.mp hi).2 (mem_singleton.mpr he)
    apply le_trans (b:=∑ a∈ (P b).support, FF b a) (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => field_sign ..))
    unfold fieldFee radius; simp only [if_neg hh, ite_true]; exact hm
  have hh : i≠o := fun he => (mem_sdiff.mp hi).2 (mem_singleton.mpr he)
  unfold fieldFee radius; simp_rw [if_neg hh,if_neg hj]; exact hk i hi hj x
include hk hm h ht hd hf hc in
private lemma each (i : V) (hi : i ∈ S\{o}) (a : Index I B) (ha : a∈ (P (f i)).support) :
    ∑ M ∈ (P i).support, FF i M * credits p q T (n+n) a M ≤ (d*K)* C i := by
  let L:= (P i).support; let W:= FF i; let c x y:= coinAt p q T (n+n) x y;
  have hl : 0 ≤ C i := by -- fix variable
    exact hc i (mem_sdiff.mp hi).1
  have ht' := zero_le_one.trans ht
  have hv : (∑ M∈L,W M*credits p q T (n+n) a M)=∑ x∈pipes a,∑ y, c x y * ∑ M∈L.filter (fun m=> y∈pipes m), W M := by
    unfold credits; simp_rw [Finset.sum_filter,Finset.mul_sum]; rw [sum_comm]; apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
    -- exchange y, restrict using guard
    have he : pipes b= Finset.univ.filter (fun y => y∈pipes b):=by ext; simp
    nth_rw 1 [he]; rw [sum_filter]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> first | exact mul_comm _ _ | simp
  rw [hv]; apply le_trans (b:=∑ _x∈pipes a,K*C i) (sum_le_sum fun x hx => ?_) (by rw [sum_const,nsmul_eq_mul,mul_assoc]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg ht' hl); exact Nat.cast_le.mpr ((card_rank a).trans (hd (f i) (hf.goes i hi) a ha)))
  apply le_trans (b:=∑ y, c x y*C i) (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (also_mark p P A E n C hk hm i hi y) (coinAt_nn ..))
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h x) hl

private def source : ℝ := ∑ a∈ (P o).support, FF o a
private def tour0 (A E : Lens T) (S : Finset V) (o b : V) (f : Parent V) := Count.tour S (fieldFee p P A E n o b)
      (fun _ a b => credits p q T (n+n) a b) f o
-- fix `tour0` notation shadow A E ok uses T via previous p?
variable {R : Census V}
variable [Fintype V]
include hk hm h ht hd hf ho hc in
lemma after_sum : ∑ M∈ Fintype.piFinset (Count.fill S (fun i => (P i).support) ∅ 0),tour0 p q P n A E S o b f M ≤
      worth (A.m ∘ p) (n+n) (P o) * (∏ i∈S\{o},(d*K)*C i) := by
  have ht' : 0 ≤ K := zero_le_one.trans ht
  apply (Count.price S (fun i=> (P i).support) (FF) (fun _ a b => credits p q T (n+n) a b) (fun i=>(d*K)*C i) f (fun _ _ _ _ => field_sign ..)
    (fun _ _ _ _ _ _ => credits_nn ..) (each p q P A E K n d h hd C hk hm ht hf hc) (fun i hi => mul_nonneg (mul_nonneg (by positivity) ht') (hc i hi)) hf ho).trans
  unfold fieldFee radius; simp only [ite_true]; exact le_rfl
-- now assemble
omit [DecidableEq I] [Fintype I] [Fintype V] in
lemma touring_count (M : V → Index I B) (ho : o∈S) : tour0 p q P n A E S o b f M =
    (∏ i∈S, FF i (M i))* beams S {o} f (fun i j => credits p q T (n+n) (M i) (M j)) := by
  rw [tour0,Count.touring,prod_mul_distrib, ← mul_prod_erase S (fun i=> FF i (M i)) ho]
  unfold beams; rw [sdiff_singleton_eq_erase]; ring -- inspect

private def pave {V K : Type} [DecidableEq V] [Zero K] (S : Finset V) (f : ↥S→ K) (i : V) : K := if h:i∈S then f ⟨i,h⟩ else 0

omit [Fintype I] [DecidableEq I] in
private lemma accounted0 (s : R.Mode) (U : (V→Index I B)→ ℝ) :
    ∑ M∈streets s P, U (pave s.val M) = ∑ M∈ Fintype.piFinset (Count.fill s.val (fun i => (P i).support) ∅ 0), U M := by
  apply Finset.sum_bij (fun i _ => pave _ i)
  · intro i hi; apply mem_piFinset.mpr; intro j; by_cases h : j∈s.val
    · simpa only [Count.fill,sdiff_empty,if_pos h,pave,dif_pos h] using mem_piFinset.mp hi ⟨j,h⟩
    simp [Count.fill,h,pave]
  · intro i hi j hj H; funext a; simpa [pave,a.property] using congr_fun H a.val
  · intro m hm; refine ⟨fun i=> m i.val, Fintype.mem_piFinset.mpr (fun i=> ?_),?_⟩;
    · simpa only [Count.fill,sdiff_empty,if_pos i.property] using mem_piFinset.mp hm i.val
    funext i; unfold pave; split; rfl; rename_i he; symm; simpa [Count.fill,he] using mem_piFinset.mp hm i
  intro _ _; rfl

variable (s : R.Mode) (hs : s.val=S) {L : ℝ} (hp : 0 ≤ L) (hL : A.Spaced E L) (ha : O.m ≤ A.m) (he : O.m ≤ E.m)
include hp hL ha he ho hb hne hs h ht hd
private lemma enrolled (M : V → Index I B) (hM : ∀ i∈S,M i∈ (P i).support) :
    tip L n * worth η n (sketch q s P fun i=> M i.val) ≤ (∑ f∈Grove.options S {o}, tour0 p q P n A E S o b f M) * rent K d S.card := by
  subst S
  rw [sketch, worth_monomial,norm_mul];
  have hh := cumulative M (schur_cov p q h) d ht s ho (fun i hi=>hd i hi (M i) (hM i hi))
  let F:= fare η n (∑ i:↥s.val,coarse (M i.val)); let Z:= ‖∏ i:↥s.val,coeff (M i.val) (P i.val)‖
  have hZ : Z=∏ i∈s.val, ‖coeff (M i) (P i)‖ := by unfold Z; rw [norm_prod,Finset.prod_coe_sort s.val (fun i => ‖coeff (M i) (P i)‖)]
  let c:= contact (fun _:V => q) (pipes ∘ M)
  have hF : 0 ≤ F := (fare_pos η (fun i => O.sign (p (Sum.inr i))) n _).le
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (norm_nonneg _)) hF) (tip_pos hp n).le).trans
  change tip L n*(F*(Z*_)) ≤ _
  rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]; refine sum_le_sum fun f hf => ?_
  let A₁ := ∏ i∈s.val,tip (w i (M i)) (n+n)
  have hr : (∏ i∈s.val,fieldFee p P A E n o b i (M i))=A₁*Z:= by rw [hZ, ← prod_mul_distrib]; rfl
  have Ht:= tipped p q M A E O n hp hL ha he ((choices ..).mp hf) ho hb hne
  change F*tip L n*beams _ _ f c ≤ A₁*_ at Ht
  rw [touring_count p q P A E n M ho,hr];
  calc
     _ = Z * (F*tip L n*beams s.val {o} f c)*rent K d s.val.card:=by ring
     _ ≤ Z * (A₁*_)*rent K d s.val.card := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Ht (norm_nonneg _)) (rent_sign d ..)
     _ = _ := by ring
include hk hm hc
-- unused include `f hf`?
theorem billed : tip L n * worth η n (track q s P) ≤
    (Grove.options S {o}).card * (worth (A.m ∘ p) (n+n) (P o) * ∏ i∈ S \ {o},(d*K)*C i) * rent K d S.card := by
  unfold track; apply (mul_le_mul_of_nonneg_left (worth_sum η (fun i => O.sign (p (Sum.inr i))) n _ _) (tip_pos hp n).le).trans; rw [Finset.mul_sum]
  subst S
  let Y (M : V → Index I B) := ∑ f ∈ Grove.options s.val {o}, tour0 p q P n A E s.val o b f M
  refine le_trans (b:=∑ M∈streets s P,Y (pave s.val M)*rent K d s.val.card) (sum_le_sum fun M hM => ?_) ?_
  · have hv : M=fun i:↥s.val=> pave s.val M i.val := by funext i; rw [pave,dif_pos i.property]
    nth_rw 1 [hv]; exact enrolled p q P A E O K n d h hd ht ho hb hne s rfl hp hL ha he _ (fun i hi=> by rw [pave,dif_pos hi]; exact mem_piFinset.mp hM ⟨i,hi⟩)
  rw [← Finset.sum_mul, accounted0 P s, ← show ∑ _f∈Grove.options s.val {o}, (worth (A.m ∘ p) (n+n) (P o)*∏ i∈s.val\{o},(d*K)*C i)=(Grove.options s.val {o}).card * (worth (A.m ∘ p) (n+n) (P o)*∏ i∈s.val\{o},(d*K)*C i) from (by simp)] -- rewrite orientation change
  apply mul_le_mul_of_nonneg_right _ (rent_sign d ..); unfold Y; rw [sum_comm]; apply sum_le_sum; intro f hf; exact after_sum p q P A E K n d h hd C hk hm ht ((choices ..).1 hf) ho hc
end YM.FormalOPE.RG10.Route
