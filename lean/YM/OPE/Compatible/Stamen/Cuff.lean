import YM.OPE.Compatible.Stamen.Garn
import YM.OPE.Compatible.Frog.Eye
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
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
section
variable (z:Bid.Dir H N)
def charW : fieldX (Shade H):=upl x (spool H N z)
omit x in
lemma inkify {ι:Type}(X:Finset ι)(v:ι→Muse H)(u:ι→ℝ) (hp:∀ i∈X,Tide (v i) d m (u i)) (x:Site N): inkM (∑ i∈X,v i) d x z= ∑ i∈X, inkM (v i) d x z:=by
       induction X using Finset.induction_on with
       | empty=> rw [Finset.sum_empty,Finset.sum_empty]; apply JetS.eta;exact flair0 ..;exact flair0 ..;exact flair0 ..
       | insert i sA h ih=> have ht(t)(h:t∈sA):=hp t (mem_insert_of_mem h); rw[sum_insert h,sum_insert h,←ih ht]; exact Ink_sum x z _ _ d _ (∑ i∈sA, u i) (hp i (mem_insert_self ..)) (by intro j; rw [Finset.sum_apply]; exact Volume.sum _ _ _ fun i hi=> ht i hi j)
lemma rayQuiet: Quiet (charW x z) 0:= quieti _ ‖spool H N z‖ (fun i=>norm_le_pi_norm (spool H N z) (x+wrap _ i.1,i.2)) (norm_nonneg _)
lemma storyP (p:Script (Shade H) k)(hp:soot m p D)(hm:2*(k+2) ≤ m)(hk:k≤d)(hh:p.abides)(ht:p.sorted):
     let V:=charW x z; inkM (Grid.lance p) d x z=⟨wholeX p (fun _=>V),Carve V (mores V 2) p,Carve V (mores V 3) p+ (2:ℝ)⁻¹*Carve2 V (mores V 2) p ⟩:=by
         intro V; let K:=inkM (Grid.lance p) d x z; have he(i: Phase): K.seq i.val= wholeX (timbre ships p (k+i.val)) (fun _=>V):=by rw [show K.seq _=_ from vein_i (Grid.lance p) d x z i]; exact throw_flair (spool H N z) (show k+i.val≤d+i.val by omega) _ x -- R rhs defeq
         apply JetS.eta
         · rw [show K.s=wholeX (timbre ships p k) (fun _=>V) from he 0, frameO hh ht hp (by omega)]
         · exact (he 1).trans (priceU p hp hm (rayQuiet x z) hh)
         exact (he 2).trans (priceB p hp hm (rayQuiet x z) hh)
lemma tokenRich (p:Seat k m (Shade H))(ht: p∈ empa H.ColorIndex k m)(hm:2*(k+2)≤m):
     let v:=charW x z; let g(i:Fin (k+1)):= inkM (Grid.lance (lilies m k (Shade H) p i.val)) k x z
     ∑ i,g i=(⟨Worth (m:=m) p v,PenD (m:=m) p v (mores v 2),PenD (m:=m) p v (mores v 3)+(2:ℝ)⁻¹ *PenD2 (m:=m) p v (mores v 2)⟩:Token):=by
         intro v g; let f(i):=lilies m k _ p i; have hz(i: Fin (k+1)):g i=⟨wholeX (f i.val) (fun _=>v),Carve v (mores v 2) (f i.val), Carve v (mores v 3) (f i.val)+(2:ℝ)⁻¹*Carve2 v (mores v 2) (f i.val) ⟩:=storyP x z _ ((sproutV m k p).2 i.val) (by have h:=i.isLt;omega) (by omega) (ht.2 _) (ht.1 _) -- adjust
         -- use Add lens
         let e(i):Token:=⟨wholeX (f i) (fun _=>v),Carve v (mores v 2) (f i), Carve v (mores v 3) (f i)+(2:ℝ)⁻¹*Carve2 v (mores v 2) (f i) ⟩; rw [sum_congr rfl (g:=fun i=> e i.val) (fun i _=>hz i),Fin.sum_univ_eq_sum_range]; apply JetS.eta
         · exact (show _ from pS e (k+1) (B:= {toFun:=JetS.s,map_add':=fun i j=> rfl,map_zero':=rfl}))
         · exact (show _ from pS e (k+1) (B:= {toFun:=JetS.l,map_add':=fun i j=> rfl,map_zero':=rfl}))
         let B:Token →+ ℝ:={toFun:=JetS.h,map_add':=fun i j=> rfl,map_zero':=rfl}; rw [show (∑ i∈range (k+1),e i).h= _ from pS e _ B]; unfold PenD PenD2; rw [mul_sum,← Finset.sum_add_distrib]; rfl
where pS (e:ℕ→Token)(k:ℕ) (B:Token →+ ℝ) : B (∑ i∈range k,e i)=∑ i∈range k,B (e i):= map_sum .. 
end
end YM.OPE.Silt.Phere
