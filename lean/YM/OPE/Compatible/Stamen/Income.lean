import YM.OPE.Compatible.Stamen.Fee
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
variable (v w:fieldX I)(hv:Quiet v 0)
include hv
lemma prize2 (p:Seat k m I)(hp:settled (m:=m) p)(h: Quiet w n)(ht:n+n ≤m): HasSum (fun a:Bunch I=> w a.1*w a.2*Worth (m:=m) (Dragon a.2 k m (Dragon a.1 k m p)) v) (PenD2 (m:=m) p v w):=by
       let f(i):=lilies m k I p i; let q(i):= Carve2 v w (f i); let g(i:ℕ)(a:Bunch I):= w a.1*w a.2*wholeX (lilies m k I (Dragon a.2 k m (Dragon a.1 k m p)) i) (fun _=>v)
       have he(i:ℕ):HasSum (g i) (q (i+2)):=by
             unfold q; rw [pillar2 (f (i+2)) (hp (i+2)) v w]; convert! ( dread v w hv (f (i+2)) ((sproutV m k p).2 _) h ht).mul_left (((i+2:ℕ):ℝ)*((i+1:ℕ):ℝ)) using 1; ext1 a; let u:=f (i+2); let A:ℝ:= i+1; unfold g; rw[dragN,dragN, show toque (((i+1+1:ℕ):ℝ) • toque (f (i+2)) a.1) a.2=((i+2:ℕ):ℝ) • toque (toque (f (i+2)) a.1) a.2 from rfl,wholeScale,wholeScale]; unfold Dial; ring
       have ht(l): k < l→ q l=0:=fun hi=>by unfold q; rw [show f l=0 from (sproutV m k p).1 l hi]; simp [Carve2,wholeX]
       have hp0 : q 0=0:=(by simp[q,Carve2]); have hp1 : q 1=0:=(by simp[q,Carve2]); -- bug
       have hb: HasSum (fun a=>∑ i ∈ range (k+1),g i a) (∑ i∈range (k+1),q (i+2)):=hasSum_sum (fun i _=>he i); convert hb using 1
       · funext a; unfold Worth; rw [mul_sum]
       unfold PenD2; change ∑ i∈range (k+1),q i=_; rw [show (∑ i∈range (k+1),q i)=∑ i∈ range (k+3),q i from by rw [sum_range_succ (f:=q) (n:=k+2),sum_range_succ (f:=q) (n:=k+1), ht (k+1) (by omega),ht (k+2) (by omega), add_zero,add_zero],sum_range_succ', sum_range_succ',hp0,hp1,add_zero,add_zero]
end YM.OPE.Silt.Phere
