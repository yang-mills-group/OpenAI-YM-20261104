import YM.SchemeRG11.Cover.Breathe
/-! Wick normal covariance. `weave` exposes the open+no-cross and all cross
 strands, no overlap estimated twice. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial Finset
open scoped Classical
variable {R S J I B : Type*} [CommRing R] [CommRing S]
namespace Dose
variable (D:Dose I R)
def weave(p q:Paper I R):Paper I R:=D.heat (D.neg.heat p*D.neg.heat q)
lemma weave_comm(p q:Paper I R): weave D p q=weave D q p:=by rw [weave,mul_comm];rfl
lemma weave_add(p q r:Paper I R): weave D (p+q) r =weave D p r+weave D q r:=by simp only [weave,map_add, add_mul]
lemma weave_smul(c:R)(p q:Paper I R):weave D (c • p) q=c • weave D p q:=by rw [weave,map_smul,smul_mul_assoc,map_smul];rfl
lemma weave_one(q:Paper I R):weave D 1 q=q:=by rw [weave,heat_one,one_mul,reverse]
lemma weave_x (u:Stem I R)(p q:Paper I R): weave D (leaf u*p) q= leaf u*weave D p q+weave D p (vent (D.windfall u) q):=by
 let m:= D.windfall u
 unfold weave; rw [zeph_neg, sub_mul, map_sub, mul_assoc,D.zephyr,D.wind,vent_l,map_add]; change _+(_+_)-_=leaf u * _+D.heat (D.neg.heat p*D.neg.heat (vent m q))
 rw [← D.neg.wind,mul_comm (vent (D.windfall u) (D.neg.heat p)) (D.neg.heat q),←add_assoc]; abel

/-- Exhaust strands in ONE factor. No Taylor order limitations on open. -/
def trail (v:J→Stem I R)(q:Paper I R)(s:Finset J):Paper I R:= (s.noncommProd (fun j=> ((vent (D.windfall (v j))).toLinearMap:Arrow I R))
  (fun i _ j _ _ => show _ by apply LinearMap.ext; intro p; exact vents ..)) q
lemma trail_empty(v:J→Stem I R)(q:Paper I R): trail D v q ∅=q:=by unfold trail; rw [Finset.noncommProd_empty];rfl
lemma trail_insert(v:J→Stem I R)(q:Paper I R) (s:Finset J)(i:J)(h:i∉s):trail D v q (insert i s)=trail D v (vent (D.windfall (v i)) q) s:=by
 unfold trail; rw [Finset.noncommProd_insert_of_notMem' _ _ _ _ h];rfl
lemma weave_power (v:J→Stem I R)(q:Paper I R)(s:Finset J):
  weave D (∏ j ∈ s,leaf (v j)) q=∑ t ∈ s.powerset,(∏ j∈s\t,leaf (v j))*trail D v q t:=by
 induction s using Finset.induction_on generalizing q with
 | empty=>rw [Finset.prod_empty,weave_one, Finset.powerset_empty, sum_singleton,sdiff_self, bot_eq_empty,prod_empty, trail_empty,one_mul]
 | insert i s hi ih=>
   rw [prod_insert hi,weave_x,ih,ih,Finset.mul_sum]
   rw [powerset_insert, Finset.sum_union,Finset.sum_image]
   · congr 1
     · apply Finset.sum_congr rfl; intro t ht
       rw [Finset.insert_sdiff_of_notMem s (show i∉t from fun w=>hi (mem_powerset.mp ht w)), prod_insert (fun w=>hi (mem_sdiff.mp w).1),mul_assoc]
     apply Finset.sum_congr rfl; intro t ht
     rw [trail_insert D _ _ _ _ (show i∉ t from fun w=>hi (mem_powerset.mp ht w))]; congr 2; ext a; by_cases h:a=i
     · rw [h]; simp [hi]
     simp [h]
   · rintro a ha b hb hab; replace ha:=mem_powerset.mp (show a∈s.powerset from ha); replace hb:=mem_powerset.mp (show b∈s.powerset from hb); simpa only [erase_insert (show i∉ a from fun w=>hi (ha w)),erase_insert (show i∉ b from fun w=>hi (hb w))] using congrArg (fun x:Finset J=>x.erase i) hab -- maybe
   rw [Finset.disjoint_left]; rintro a ha he; obtain ⟨b,_,hb⟩:=mem_image.mp he; subst a; exact hi ((mem_powerset.mp ha) (mem_insert_self i b))
lemma weave_null(p q:Paper I R):D.neg.heat (D.weave p q)= D.neg.heat p * D.neg.heat q:=D.opposite _
end Dose
end YM.SchemeRG11.Haze
