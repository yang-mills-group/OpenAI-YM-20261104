import YM.OPE.Compatible.Stamen.Lop
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
local notation "R!"=> Root I
abbrev unicorn (I:Type)(k:ℕ):Root I×Page I k ≃ Page I (k+1):= {
      toFun p:=Fin.cons p.1 p.2
      invFun v:=(v 0,mort v)
      left_inv:=fun x=> by simp only [Fin.cons_zero,mort,Fin.tail_cons]
      right_inv:=fun y=> Fin.cons_self_tail _ }
-- explicit integral vortex.B.
section
variable (v w:fieldX I)(hv:Quiet v 0)
abbrev bilk (p:Script I (k+1))(a:R!):= w a * wholeX (toque p a) (fun _=>v)
abbrev Dial (p:Script I (k+2))(x:Bunch I):= w x.1*w x.2*wholeX (toque (toque p x.1) x.2) (fun _=>v)
lemma xfum (u:Fin k→fieldX I)(t:fieldX I)(p:Page I (k+1)): wordX (Fin.cons t u) p=t (p 0)*wordX u (mort p):=Fin.prod_univ_succ _
include hv
lemma fear (p:Script I (k+1))(hp: soot m p C)(ht:Quiet w n)(h:n≤m): HasSum (bilk v w p) (wholeX p (Fin.cons w (fun _=>v))):=by
      let a:Fin k→fieldX I:=fun _=>v; let V:= (Fin.cons w a:Fin (k+1)→fieldX I); let A(i:Page I (k+1)):= p i*wordX V i; let K(i:Root I×Page I k):=A (unicorn I k i)
      let U:= (Fin.cons n (fun _:Fin k=>0):Fin (k+1)→ℕ); have ht':Glob V U:=by
            intro i; refine Fin.cases ?_ (fun t=> ?_) i
            · unfold U V; rw[Fin.cons_zero,Fin.cons_zero]; exact ht
            unfold U V; rw[Fin.cons_succ,Fin.cons_succ]; exact hv
      have hu : ∑ i,U i≤m:=by rw[Fin.sum_univ_succ]; simp [U]; omega
      have hx : Summable A:= wordSum hp ht' hu
      have hz: Summable K:= (unicorn I k).summable_iff (f:=A) |>.mpr hx
      have hx(i:R!)(j:Page I k): K (i,j)= w i* (toque p i j*wordX a j):=by unfold K A; rw [show wordX V (unicorn I k (i,j))= _ from xfum a w _]; simp only[toque,mort,unicorn,Equiv.coe_fn_mk, Fin.cons_zero,Fin.tail_cons]; ring
      have hr(i:R!): bilk v w p i=∑' j:Page I k,K (i,j):= by simp_rw [hx,tsum_mul_left]; rfl
      rw [funext hr]; convert! hz.prod.hasSum using 1; rw [← hz.tsum_prod]; exact ((unicorn I k).tsum_eq A).symm
lemma dread (p:Script I (k+2))(hp:soot m p C)(ht:Quiet w n)(h:n+n≤m): HasSum (Dial v w p) (wholeX p (Fin.cons w (Fin.cons w (fun _=>v)))):=by
      let a:Fin k→fieldX I:=fun _=>v; let b:Fin (k+1)→fieldX I:=Fin.cons w a; let V:= (Fin.cons w b:Fin (k+2)→fieldX I); let A(i:Page I (k+2)):= p i*wordX V i; let K(i:Bunch I×Page I k):=A (peacock I k i)
      let Y: Fin (k+1)→ℕ:=Fin.cons n (fun _:Fin k=>0); let U:= (Fin.cons n Y:Fin (k+2)→ℕ)
      have hb :Glob b Y:=by
           intro i; refine Fin.cases ?_ (fun i=>?_) i
           · unfold b Y; rw[Fin.cons_zero,Fin.cons_zero]; exact ht
           unfold b Y; rw[Fin.cons_succ,Fin.cons_succ]; exact hv
      have hh:Glob V U:=by
            intro i; refine Fin.cases ?_ (fun t=>?_) i
            · unfold U V; rw[Fin.cons_zero,Fin.cons_zero]; exact ht
            unfold U V; rw[Fin.cons_succ,Fin.cons_succ]; exact hb _
      have hz:Summable K:= (peacock I k).summable_iff (f:=A) |>.mpr (wordSum hp (u:=V) (k:=U) hh  (by rw [Fin.sum_univ_succ]; simp only[U,Y,Fin.cons_zero,Fin.cons_succ,Fin.sum_univ_succ,Finset.sum_const_zero,Nat.add_zero];exact h))
      have hx(i:Bunch I)(j:Page I k): K (i,j)= w i.1*w i.2* (toque (toque p i.1) i.2 j*wordX a j):=by unfold K A; rw [show wordX V (peacock I k (i,j))= _ from xfum b w _,show wordX b _=_ from xfum a w _]; simp only[mort,peacock,usher,toque, Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons];ring
      have hr(i:Bunch I): Dial v w p i=∑' j:Page I k,K (i,j):= by simp_rw [hx,tsum_mul_left]; rfl
      rw [funext hr]; convert! hz.prod.hasSum using 1; rw [← hz.tsum_prod]; exact ((peacock I k).tsum_eq A).symm
omit hv
lemma wholeScale (p:Script I k)(t:ℝ)(a:Fin k→fieldX I):wholeX (t • p) a = t * wholeX p a:=by unfold wholeX; rw [← tsum_mul_left]; refine tsum_congr (fun i=>?_); change t*_ * _= _ ;ring
-- Locus Seat freeze fiscal
abbrev Worth (p:Seat k m I) (v:fieldX I):ℝ:=∑ i∈ range (k+1),wholeX (lilies m k I p i) (fun _=> v)
abbrev PenD (p:Seat k m I) (v w:fieldX I):ℝ:=∑ i∈ range (k+1),Carve v w (lilies m k I p i)
abbrev PenD2 (p:Seat k m I) (v w:fieldX I):ℝ:=∑ i∈ range (k+1),Carve2 v w (lilies m k I p i)
include hv
lemma prize (p:Seat k m I)(hp:settled (m:=m) p)(h:Quiet w n)(ht:n≤m): HasSum (fun a:R!=> w a*Worth (m:=m) (Dragon a k m p) v) (PenD (m:=m) p v w):=by
      let f:= lilies m k I p; let T(i:ℕ)(a:R!):= w a*wholeX (lilies m k I (Dragon a k m p) i) (fun _=>v); have hz(i): HasSum (T i) (Carve v w (f (i+1))):=by
           rw [pillar (f (i+1)) (hp (i+1)) v w]; convert! (fear v w hv (f (i+1)) ((sproutV m k p).2 _) h ht).mul_left ((i+1:ℕ):ℝ) using 1; ext1 a; unfold T; rw [dragN, wholeScale]; unfold bilk; unfold f;ring
      have hj: Carve v w (f 0)=0:=(by simp [Carve]); rw [PenD, show lilies m k I p=f from rfl, sum_range_succ',hj,add_zero]
      rw [show (∑ i∈range k, Carve v w (f (i+1)))=∑ i∈range (k+1),Carve v w (f (i+1)) from by rw [sum_range_succ,(show f (k+1)=0 from (sproutV m k p).1 _ (by omega)),show Carve _ _ (0:Script I (k+1))=0 from by simp only [Carve,wholeX, Pi.zero_apply,zero_mul,tsum_zero,sum_const_zero],add_zero]]; simpa only [Worth,mul_sum] using! hasSum_sum (s:=range (k+1)) (fun i _=>hz i)
end
end YM.OPE.Silt.Phere
