import YM.SchemeRG11.Outer.Light
/-! The f_i finite sector sums and retagging. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt Sew
open scoped Classical Pointwise
variable {I:Type}{G:Gauge} (s:Finset I) (p:I→ pLabel G) {n m:ℕ}{T: Align.Itinerary}
local notation "D₁"=> Atoll.land G
lemma district(v:I→ vellum G)(t:I→ Cover)(o:Cover): aerial s v t=cross o (aerial s v (fun i=> t i-o)):=by
 unfold aerial; rw [map_prod]; apply Finset.prod_congr rfl; intro i hi; rw [cross_sum,add_comm o,sub_add_cancel]
def nearTag (B:Window)(t: Landmarks I)(T: Itinerary)(o:I)(j k:Axis)(R:ℝ)(i:ℕ):=∑ x∈gateY T R i, cove T B i x * turnup s (fun l=>castZero (T.gap i) (p l)) (fun l=>t l i) j k (x+t o i)
variable [Fintype I]
lemma packs(B:Window)(t:Landmarks I)(T: Itinerary)(j k: Axis){r:ℝ}(h:B.rOut<r):∀ᶠ i in atTop,
 let u:= turnup s (fun l=>castZero (T.gap i) (p l)) (fun l=>t l i) j k
 (∑' x, u x)=(∑' x, rest T B s t i x*u x)+∑ o∈s,nearTag s p B t T o j k r i:=by
 filter_upwards [past (T:=T) h] with i hi; intro u
 let U(o:I)(x:Cover):=cove T B i (x-t o i)*u x
 let S:=gateY T r i
 have hh(o:I)(x:Cover)(hx:x∉ S.image (fun k=> k+t o i)): U o x=0:=by
    have hp:cove T B i (x-t o i)=0:=by contrapose! hx; exact Finset.mem_image.mpr ⟨x-t o i,(gate_iff ..).mpr (hi _ hx),sub_add_cancel ..⟩
    unfold U; rw [hp,zero_mul]
 have he(o:I):Summable (U o):= summable_of_ne_finset_zero (hh o)
 have hz(o:I): ∑' x,U o x= nearTag s p B t T o j k r i:=by
   rw [tsum_eq_sum (hh o),Finset.sum_image]; · unfold nearTag U; simp only [add_sub_cancel_right]; rfl
   exact fun _ _ _ _ h=>add_right_cancel h
 unfold rest; simp_rw [sub_mul, one_mul, Finset.sum_mul]; change _=(∑' x, (u x - (∑ o∈s,U o x)))+_
 rw [Summable.tsum_sub (show Summable u from luggage ..) (summable_sum (fun i _=>he i)),Summable.tsum_finsetSum (fun i _=>he i)]; simp_rw [hz, sub_add_cancel] -- names
omit [Fintype I] in
lemma plume_s (z:ℕ){x:pLabel G}(h:IsWeightedHomogeneous generation x z)(T:ℝ): stemZero T x=T^(-(z:ℤ)) • stemZero 1 x:=by rw [← (expand_sc T x).2, programDeg T _ h, map_smul, zpow_neg,zpow_natCast,inv_pow]
variable [DecidableEq I]
omit [Fintype I] in
lemma switch(o:I)(t:I → Cover)(h:ℝ)(x:vellum G):
 (D₁).avg (cross (t o) x*aerial (s.erase o) (fun i=>castZero h (p i)) t)=(D₁).avg (x* aerial (s.erase o) (fun i=>castZero h (p i)) (fun i=>t i-t o)):=by rw [district _ _ t (t o),←map_mul (cross (t o)),cross_cov]
def motionP(t:Landmarks I)(o:I):Landmarks I:=fun i k=> t i k-t o k
omit [Fintype I] in
lemma placement(t:Landmarks I)(o:I)(ho:o∈s)(i:ℕ)(h:ℝ)(x:Cover)(j k:Axis):
 turnup s (fun l=>castZero h (p l)) (fun l=>t l i) j k (x+t o i)= (D₁).avg (Tree.cost x j k * castZero h (p o) * aerial (s.erase o) (fun l=>castZero h (p l)) (fun l=>motionP t o l i)):=by
 unfold turnup; rw [aerial,← Finset.mul_prod_erase _ _ ho]
 rw [add_comm x (t o i), ← honour (G:=G) (t o i + x) j k,←cross_sum,honour,←mul_assoc,←map_mul (cross (t o i))]
 exact switch ..
end YM.SchemeRG11.Dock
