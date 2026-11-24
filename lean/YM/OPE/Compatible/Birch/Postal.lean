import YM.OPE.Compatible.Birch.Yucca
/-! # Stencil Lipschitz -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W K:Type*} {i j n r d m:ℕ}{G:Gauge}{s b U D t ε:ℝ}{N:Side}
namespace Script
open Page
variable {p p':K→Script I (r+1)}{q q':K→Script I (d+1)}{A A': K→Row I I}{u v w X:K→ℝ}
section
variable {V Y:I→ℝ}{f g:I→ℝ}{Z:I→J}
lemma shedB [DecidableEq J](Z:I→J)(h: Summable f)(hx: Summable g): Sack.rope Z (f-g)= Sack.rope Z f-Sack.rope Z g:=by
   have he: Sack.rope Z (-g)=- Sack.rope Z g:=by
       ext1 i; change (∑' j, if Z j=i then (-g) j else _) = -(∑' j,_); rw [← tsum_neg]; refine tsum_congr fun j=>?_ ; split_ifs; rfl;simp
   rw [sub_eq_add_neg,Sack.rope_add Z h (show Summable (-g) from hx.neg),he,sub_eq_add_neg]
end
lemma trellisTurn (h:Loan m p u X)(hp:Loan m q v X)(he:Tip s A w X)(hs:0<s)(hg:0≤w)(hh:1 ≤ X):Loan m (fun i=>cotton (A i) (p i) (q i)) (u*v*w) X:=by
    obtain ⟨a,ha,f,h'⟩:=h; obtain ⟨b,hb,g,H⟩:=hp; obtain ⟨c,hc,k,T⟩:=he; let C:=widthCost s m; refine ⟨a*b*c*C*((3*d+2:ℕ):ℝ)^m,by have ht:0 ≤ C:=zero_le_one.trans (widthCost_ge hs m); positivity,f+g+k,fun i=>(cotton_cost (T i) hs (show 0 ≤ _ from mul_nonneg (mul_nonneg hc (pow_nonneg (zero_le_one.trans (hh i)) _)) (hg i)) (h' i) (H i)).tips (le_of_eq ?_)⟩; simp only [C,Pi.mul_apply]; ring
lemma tosser {p q:Script I (r+1)}{A:Row I I}{g:Script I (d+1)}(h:Summable p)(hg:Summable q)(he:Whole A)(hz:Summable g): cotton A p g - cotton A q g=cotton A (p-q) g:=by
    unfold cotton; rw [← shedB _ (cotton_s he h hz) (cotton_s he hg hz)]; apply congr_arg; ext i; unfold ticketX; simp only [Pi.sub_apply];ring
lemma tressing {p q:Script I (r+1)}{A:Row I I}{g:Script I (d+1)}(h:Summable p)(hg:Summable q)(he:Whole A)(hz:Summable g): cotton A g p - cotton A g q=cotton A g (p-q):=by
    unfold cotton; rw [← shedB _ (cotton_s he hz h) (cotton_s he hz hg)]; apply congr_arg; ext i; unfold ticketX; simp only [Pi.sub_apply];ring
lemma tar {p:Script I (r+1)} {A B:Row I I}{g:Script I (d+1)}(h:Summable p)(he:Whole A)(hb:Whole B)(hz:Summable g): cotton A p g - cotton B p g=cotton (A-B) p g:=by
    unfold cotton; rw [← shedB _ (cotton_s he h hz) (cotton_s hb h hz)]; apply congr_arg; ext i; unfold ticketX; simp only [Pi.sub_apply];ring
lemma loadedCot (hs:0<s)(h:1 ≤ X)(hx:0 ≤ u)(ha:Tip s A 1 X)(hc:Tip s A' 1 X)(he:Tip s (A-A') u X)(hp:Loan m p 1 X)(hp':Loan m p' 1 X)(hq:Loan m q 1 X)(hq':Loan m q' 1 X) (hz:Loan m (p-p') u X)(hw:Loan m (q-q') u X): Loan m (fun i=> cotton (A i) (p i) (q i)-cotton (A' i) (p' i) (q' i)) u X:=by
    have h1:=trellisTurn hz hq ha hs zero_le_one h; have h2:=trellisTurn hp' hw hc hs zero_le_one h; have h3 := trellisTurn hp' hq he hs hx h
    simp only [mul_one,one_mul] at h1 h2 h3
    have H:= (h1.seize h2 h hx).seize h3 h hx
    rw [show (fun i=>cotton _ (p i) (q i)-cotton _ (p' i) (q' i))= _ from ?_]; exact H
    funext i; obtain ⟨a,b,u,P⟩:= ha; obtain ⟨a',b',v,Q⟩:=hc
    have h: Whole (A i):=⟨_,_,hs,P i⟩; have hv:Whole (A' i):=⟨_,_,hs,Q i⟩
    simp only [Pi.sub_apply,Pi.add_apply]; rw [← tosser (sootS (hp.bill i).choose_spec) (sootS (hp'.bill i).choose_spec) h (sootS (hq.bill i).choose_spec), ← tressing (sootS (hq.bill i).choose_spec) (sootS (hq'.bill i).choose_spec) hv (sootS (hp'.bill i).choose_spec), ← tar (sootS (hp'.bill i).choose_spec) h hv (sootS (hq.bill i).choose_spec)]; abel
-- self
variable {f g:K→Script I (r+2)}
lemma fuse_self (hs:0<s)(h:1 ≤ X)(hx:0≤u)(ha:Tip s A u X)(hp:Loan m f v X) : Loan m (fun i=>pad (A i) (f i)) (u*v) X:=by
    obtain ⟨c,hc,t,P⟩:=ha; obtain ⟨b,hb,y,H⟩:=hp; refine ⟨c*b,mul_nonneg hc hb,t+y,fun i=> (pad_charge (P i) hs.le (show 0 ≤_ from mul_nonneg (mul_nonneg hc (pow_nonneg (zero_le_one.trans (h i)) _)) (hx i)) (H i)).tips ?_⟩; rw [Pi.mul_apply]; exact le_of_eq (by ring)
lemma tunnelS {f:Script I (r+2)}(h:Summable f) {A:Row I I}(he:Whole A):Summable (tunnel A f):=by obtain ⟨s,c,hs,g⟩:=he; exact sootS (tunnel_budget (strip_mono g le_rfl (le_max_left ..)) hs.le (le_max_right c 0) (Tsumm h))
lemma fuse_d (hs:0<s)(h:1 ≤ X)(hx:0≤u)(ha:Tip s A 1 X)(hb:Tip s A' 1 X)(hp:Loan m f 1 X)(hP:Loan m g 1 X)(hh:Tip s (A-A') u X)(hk:Loan m (f-g) u X): Loan m (fun i=> pad (A i) (f i)-pad (A' i) (g i)) u X:=by
    have h1:=fuse_self hs h (u:=1) zero_le_one ha hk; have h2:=fuse_self hs h hx hh hP; rw [one_mul] at h1; rw [mul_one] at h2; have H:=h1.seize h2 h hx; rw [show (fun i=>pad (A i) (f i)-pad (A' i) (g i))=_ from ?_]; exact H
    ext1 i; obtain ⟨c,hc,n,P⟩:=ha; obtain ⟨b,hZ,t,R⟩:=hb; have hv:Whole (A i):=⟨_,_,hs,P i⟩; have he:Whole (A' i):=⟨_,_,hs,R i⟩; have hf:=sootS (hp.bill i).choose_spec; have hg:=sootS (hP.bill i).choose_spec
    unfold pad; rw [Pi.add_apply,← shedB _ (tunnelS hf hv) (tunnelS hg he), ← Sack.rope_add _ (tunnelS (f:=(f-g) i) (hf.sub hg) hv) (tunnelS (A:=(A-A') i) hg (hv.minus he))]; apply congr_arg; ext1 j; simp only [Pi.add_apply,Pi.sub_apply,tunnel];ring
end Script
end YM.OPE.Flume
