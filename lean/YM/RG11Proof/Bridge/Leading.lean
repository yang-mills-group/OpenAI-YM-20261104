import YM.RG11Proof.Bridge.Gram
/-! Leading absorption from reusable two-slot `Saves` receipts, e.g.
instantiate with the REAL parts of reflected separated test profiles after
pulling back reflection on the field indices (not assumed done automatically).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bridge
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal YM.RG11.Rate Filter
open scoped BigOperators Classical
variable {α J : Type*} [Fintype J] [DecidableEq J] {k : Budget α}
local notation "PS"=>PowerSeries ℝ
abbrev two : Unit→ℕ:=fun _=> 2
def pair (i j:J): Mark J two:=⟨(),![i,j]⟩

omit [DecidableEq J] in
private theorem read_pairs0 (D : ArrayAt J ℝ two) (T : Change ℝ J) (h : Anchored T.g) (i j : J) :
    constantCoeff (T.act D (pair i j)) = ∑ u, ∑ v,
       constantCoeff (D (pair u v)) * (piece 0 T.Z i u * piece 0 T.Z j v) := by
  rw [Change.act,PertExtension.Position.insert_constant]
  simp_rw [base_compose _ _ h, piece_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  -- rewrite insert sum over fin2 function as double sum
  unfold PertExtension.Position.insert
  trans ∑ w: Fin 2 → J, constantCoeff (D ⟨(),w⟩) * (constantCoeff (T.Z i (w 0))*constantCoeff (T.Z j (w 1)))
  · simp only [pair,two,Fin.prod_univ_two]; rfl
  rw [← Equiv.sum_comp (finTwoArrowEquiv J).symm,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_; intro u _; refine Finset.sum_congr rfl ?_; intro v _
  simp [pair,finTwoArrowEquiv_symm_apply]

omit [DecidableEq J] in
private theorem row_price (Z : α→Square J ℝ) (i j:J): Burden k (priceRow Z i) (fun a=>Z a i j):=
   (Burden.self ..).dominated (Eventually.of_forall (fun a=> by
     unfold priceRow; rw [abs_of_nonneg (a:= ∑ j,|Z a i j|) (Finset.sum_nonneg fun _ _=> abs_nonneg _)]
     exact Finset.single_le_sum (fun l _=>abs_nonneg (Z a i l)) (Finset.mem_univ _)))

-- Bound product over any submask of two-slot object; require boundedness
-- on the second slot only and never presume zero of the arbitrary first.
omit [DecidableEq J] in
private theorem two_cost (T : α→Change ℝ J) (i j:J)
    (hd : ∀ l, Bounded k (fun a=> piece 0 (T a).Z j l)) (w:Fin 2→J) (s:Finset (Fin 2)):
    Burden k (priceRow (fun a=> piece 0 (T a).Z) i)
      (fun a=> ∏ l∈s, constantCoeff ((T a).Z (![i,j] l) (w l))) := by
  let f(a:α)(l:Fin 2):=piece 0 (T a).Z (![i,j] l) (w l)
  simp_rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change Burden k _ (fun a=> ∏ l∈s, f a l)
  have hy(a): (∏ l∈s, f a l)=(if (0:Fin 2)∈s then f a 0 else 1)*(if (1:Fin 2)∈s then f a 1 else 1):=by
    rw [← Fin.prod_univ_two (fun l=> if l∈s then f a l else 1), ← Finset.prod_filter]
    simp
  simp_rw [hy]
  let W := priceRow (fun a=>piece 0 (T a).Z) i
  have hv : Burden k W (fun a=> f a 0) := row_price _ i (w 0)
  have hr : Bounded k (fun a=> f a 1):= hd (w 1)
  refine Burden.mult_right ?_ ?_
  · split_ifs with h <;> first | exact hv | exact Burden.of_bounded (Bounded.const _)
  split_ifs with h <;> first | exact hr | exact Bounded.const _

private theorem row_compare (V D : α→ArrayAt J ℝ two) (A : ArrayAt J ℝ two) (i j:J)
    (T : α→Change ℝ J) (hb:∀ a,Anchored (T a).g)
    {m : Finset (Mark J two)} (hm : pair i j∈m)
    (he:Saves k 0 m V D T)
    (hV : ∀ u v,Crest k 0 V A (pair u v)) (hD : Crest k 0 D A (pair i j))
    (hd:Done k (fun a=>piece 0 (T a).Z) j) :
    let Z(a:α): Square J ℝ:=piece 0 (T a).Z
    let F(u v:J):=constantCoeff (A (pair u v))
    Carry k (priceRow Z i) (fun _=>F i j) (fun a=>∑ l,Z a i l * F l j):=by
  intro Z F
  let W := priceRow Z i
  have hT : Carry k W (fun a=> constantCoeff (tail (he.bits a) (T a).Z (pair i j))) (fun _=>0) := by
    simp only [tail,map_sum]
    rw [show (fun _ : α=> (0:ℝ))=(fun _=> ∑ _ : Finset (Fin 2), ∑ _ : Fin 2→J,(0:ℝ)) from by simp]
    change Carry k W (fun a=>∑ u : Finset (Fin 2), _) _
    refine carry_sum (fun u _=>?_)
    by_cases h:u=∅
    · simp_rw [if_pos h,map_zero,Finset.sum_const_zero]; exact Carry.refl _
    simp_rw [if_neg h,map_sum,map_mul,map_prod]; refine carry_sum fun w _=>?_ -- map_sum may no occurrence until split
    have hw:= (he.slips hm u (Finset.nonempty_iff_ne_empty.mpr h) w).price (i:=0) le_rfl
    simp_rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_zero] at hw
    have ht:=Carry.of_mul_uncertain hw (two_cost T i j (fun l=>(hd l).bounded) w (Finset.univ\u))
    simpa only [pair,zero_mul] using ht
  have hMain : Carry k W (fun a=> constantCoeff ((T a).act (V a) (pair i j))) (fun a=>∑ l,Z a i l * F l j):= by
    simp_rw [read_pairs0 _ _ (hb _)]
    have hp(a:α): (∑ l,Z a i l*F l j)=∑ l:J,∑ v:J,F l v * (Z a i l*(1:Square J ℝ) j v):= by
      classical
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun b _ hb=>by rw [Matrix.one_apply_ne hb.symm,mul_zero,mul_zero]), Matrix.one_apply_eq,mul_one,mul_comm]
    simp_rw [hp]; refine carry_sum (fun l _=> carry_sum (fun v _=>?_))
    have ht' : Near k (fun a=>constantCoeff (V a (pair l v))) (F l v) := by unfold F; simp_rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact (hV l v).price (i:=0) le_rfl
    have ht : Near k (fun a=> constantCoeff (V a (pair l v)) * piece 0 (T a).Z j v) (F l v * (1:Square J ℝ) j v) := ht'.mul (hd _)
    have hu := Carry.of_mul_uncertain ht (row_price (k:=k) Z i l)
    convert! hu using 1 <;> ext a <;> ring
  have hw:= (hD.price (i:=0) le_rfl).symm
  have hz:= he.values (i:=0) le_rfl _ hm
  simp_rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_add] at hw hz
  have hx : Carry k W (fun _=>F i j) _ := (hw.trans hz).carry W
  exact hx.trans (by simpa only [add_zero] using hMain.add hT)

-- All two-profile inputs here in one shape; embed into larger demand using
-- operations on Saves and K-closure or supply independently on the side.
-- In particular `pair` readouts of V,D must already carry the geometric
-- reflection (if any); using unreflected profiles with no compensating
-- matrix action may violate Positive. R is the fixed remnant action on field
-- indices on the second leg only. No requirement that finite T commutes it.
theorem leading_of_paired (A : ArrayAt J ℝ two) (V D : α→ArrayAt J ℝ two) (d : J→ℕ)
    (T : α→Change ℝ J) (hT : ∀ a, Anchored (T a).g) (R: Square J ℝ)
    (hR:∀ i j,d i< d j → R i j=0)
    (hg : Positive (Matrix.of fun i j=> constantCoeff (A (pair i j))) R)
    (Y : Finset (Mark J two)) (hY:∀ i j,d j<d i → pair i j∈Y)
    (he:Saves k 0 Y V D T)
    (hV : ∀ i j,Crest k 0 V A (pair i j)) (hD:∀ i j,d j<d i → Crest k 0 D A (pair i j))
    (hq:∀ i j,d i ≤ d j → Near k (fun a=>piece 0 (T a).Z i j) ((1:Square J ℝ) i j)) :
    ∀ i,Done k (fun a=>piece 0 (T a).Z) i := by
  apply gram_leading _ hg hq
  intro i H j hj
  unfold gramAt; simp only [Matrix.of_apply,Finset.mul_sum]
  rw [show (fun a:α=> ∑ l,∑ m,piece 0 (T a).Z i l * (R j m * constantCoeff (A (pair l m))))=_ from funext fun _=> Finset.sum_comm]
  let Z(a:α): Square J ℝ:=piece 0 (T a).Z
  let f(l n:J):=constantCoeff (A (pair l n))
  change Carry k _ (fun a=>∑ l:J,∑ m:J,Z a i m * (R j l * f m l)) (fun _=> ∑ l,R j l * f i l)
  refine carry_sum (fun l _=> ?_)
  by_cases ht: R j l=0
  · simp_rw [ht,zero_mul,mul_zero,Finset.sum_const_zero]; exact Carry.refl _
  have hh:d l<d i:= lt_of_le_of_lt (le_of_not_gt (fun h=>ht (hR _ _ h))) hj
  have he:=Carry.mul_bounded (row_compare V D A i l T hT (hY i l hh) he hV (hD _ _ hh) (H l hh)).symm
       (Bounded.const (R j l))
  convert! he using 1 <;> ext a
  · rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; change Z a i m*(R j l*f m l)=Z a i m*f m l*(R j l); ring
  exact mul_comm ..
end YM.RG11.Bridge
