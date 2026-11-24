import YM.MS.Orbit.L_Ready

/-!
Transport a no-momentum-conservation vertex on the lattice cover from its presentation at a
common anchor c to an anchor c+A, and vice versa. Work here in strictly periodic symbols.
Addition of phases to kernels does NOT force any mesh momentum projection. Used for identifying
the two (different infrared continuations of the) cover log equations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet

open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge} {I:Type} {L:I→Side}
variable {μ:Measure QP}{F H:Law G}{P:Latch.Edge G}
  {x y z:Lengths G}
local notation "pQ"=> field (parity (C:=G.ColorIndex) (A:=Axis))

lemma be_mom (A:Cover)(p q:QP): be A (p+q)=be A p*be A q:= rightadd ..
lemma be_add (A B:Cover)(p:QP): be (A+B) p=be A p*be B p:= by rw [be,emb_add,payadd]
lemma be_sub (A B:Cover)(p:QP): be (A-B) p=be A p*(be B p)⁻¹:= by rw [sub_eq_add_neg,be_add,show be (-B) p=(be B p)⁻¹ from (by unfold be; rw [emb_neg,Tone.opp])]
lemma be_0 (p:QP): be 0 p=1:= by simp [be, embed, Tone.bill,pairing] -- namespace pairing
lemma be_mneg (A:Cover)(p:QP): be A (-p)= (be A p)⁻¹:= Tone.inverse ..
lemma be_n (A:Cover)(p:QP): be A p≠0:= nonz _ _

def lodging (A:Cover) : Op (Lane4 G) ℂ:= {
  toFun F:= fun l=> be A (net l)*F l
  map_add' _ _:= funext fun _=> mul_add ..
  map_smul' _ _:= funext fun _=> mul_left_comm .. }
lemma lodg (A:Cover)(F:Law G) (l:Lengths G): lodging A F l=be A (net l)*F l:=rfl
lemma home_0 (A:Cover): lodging A F []=F []:= by rw [lodg,show net ([]:Lengths G)=0 from rfl]; simp [be]
lemma house (A B:Cover): lodging A (lodging B F)=lodging (A+B) F:= by ext; simp_rw [lodg,be_add,mul_assoc]
lemma pure : lodging 0 F=F:= funext fun w=> by rw [lodg,be_0,one_mul]
lemma unpack_home (A:Cover): sleeve weightψ ( lodging (-A) (lodging A ( sleeve lace F )))=F:= by rw [house, neg_add_cancel,pure]; ext; rw [sleeve_here,sleeve_here,← mul_assoc,hook_c, one_mul]
lemma pack_home (A:Cover): lodging A ( sleeve lace ( sleeve weightψ ( lodging (-A) F )))=F:= by
   rw [ show sleeve lace (sleeve weightψ (lodging (-A) F))=lodging (-A) F from ?a,house,add_neg_cancel,pure ]; ext; rw [sleeve_here,sleeve_here,← mul_assoc, mul_comm (hook lace _),hook_c,one_mul]

lemma be_tr (A:Cover)(w:Lengths G)(q:QP): trc P q (lodging A F) w=be A (net w)*trc P q F w:= by
  simp_rw [at_trc,lodg,net_cons,← add_assoc,add_neg_cancel,zero_add,mul_left_comm (P _ _ _),Finset.mul_sum]
lemma be_cycle (A:Cover): cycle P μ (lodging A F)= lodging A (cycle P μ F):= by funext l; unfold cycle; simp_rw [be_tr,integral_const_mul]; rfl
lemma be_tree (A:Cover) (h:Reverse P parity): tree parity P H (lodging A F)=lodging A (tree parity P H F):= by
    funext l; unfold tree; let T:= allocate pQ l ( R:=ℂ ); rw [lodg]; change T _= (_ :ℂ) • T (attaches _ _ _ _); rw [← map_smul]; refine scatter_congr _ _ _ _ (fun x y he=>?_); obtain hT:= split_net he; simp only [Pi.smul_apply, smul_eq_mul, convertR h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; simp only [radius,neg_neg,lodg,net_cons,hT]; ring

private lemma be_join (A B:Cover) (l r:Lengths G)(i j:BH G) (q:QP): viν false P i j (lodging A F) (lodging B H) l r q=
     be A (net l)*be B (net r)*(be (A-B) q * viν false P i j F H l r q):= by
    unfold viν; simp_rw [lodg,net_cons, show Opp false q=-q from rfl, be_mom, be_mneg, be_sub]; ring
lemma joint (A B:Cover): PairV false μ 0 0 P (lodging A F) (lodging B H)= lodging B (PairV false μ (A-B) (A-B) P F H):= by
    funext l; unfold PairV; let T:= allocate pQ l ( R:=ℂ ); rw [lodg]; change T _= (_ :ℂ) • T _; rw [← map_smul]; refine scatter_congr _ _ _ _ (fun x y he=>?_); obtain hT:= split_net he; simp_rw [ be_join, be_0,one_mul,integral_const_mul, ← Finset.mul_sum,Pi.smul_apply, smul_eq_mul]
    rw [← hT,be_mom,be_sub]; field_simp [be_n]

end YM.MS.Fleet
