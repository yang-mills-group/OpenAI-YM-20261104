import YM.MSbar.Lis.Medals
import YM.MSbar.Lis.Meadows
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Wilson
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{a b Y V Z Q w:ℝ}{p h i m r v:ℕ}
local notation "W"=>Positions (Primary n G)
local notation "K"=>Primary n G
variable (S:Nesting G n)(R:PathData G) (l:Clip)
noncomputable def atlas (S:Nesting G n)(p r:ℕ)(R:PathData G) (l:Clip):Positions (Primary n G)→ℝ:= joy (tariff n p l R S) r
variable (x:Primary n G)(s:Strand G)
local notation "X"=>fun i=>atlas S p i R l
local notation "H"=> fun k=> buoy (atlas S p k R l) 0
noncomputable def statue (G:Gauge)(r m:ℕ) := ∑ i∈Finset.range r,medal G m (r-i)
local notation "fΣ"=>statue G r
local notation "Ch₀"=> swipe (Measuring.chart n G) b v
lemma statue_pos (G:Gauge)(r m:ℕ):0 ≤ statue G r m:= Finset.sum_nonneg fun i _=> mpos ..
variable {F:ℝ→ Config G n→ℝ}(hF:Trend F S R l p)
variable (hr:r≤p)(hk:2≤v)(hx:0≤b)(hZ:∀ i< r,∀ y':Primary n G,∀ j,j≤ m+1→Yarn j (fun L:List (Primary n G)=> |buoy (atlas S p i R l) 0 (y'::L)| *swipe (Measuring.chart n G) b v (y'::L))≤Z)
include hF hr hk hx hZ
lemma titled : Yarn m (fun L:List K=> tide (x::L)*|buoy (deck (X r) x s) 0 (x::L)|) ≤ statue G r m*Z:=by
    let P i:= optics (r-i) (X i) (ace x s); have he: deck (X r) x s= fun z=>(-1:ℝ)*∑ i∈Finset.range r, P i z:=by
        funext z; rw [neg_one_mul]; exact driven R l S p hF r hr z (ace x s)
    have hX(i:ℕ)(t:ℕ): ContDiffAt ℝ t (X i) 0:= (Cacao.vent ..).contDiffAt.of_le le_top
    have ht(i:ℕ): ContDiffAt ℝ (↑(m+1:ℕ)) (P i) 0:= rose (X i) _ (m+2) _ (hX i _) le_rfl _
    -- Lis.tot requires Fintype ℕ. add lemma
    refine le_trans (b:=∑ i∈Finset.range r,Yarn m (fun L=> tide (x::L)*|buoy (P i) 0 (x::L)|)) ?_ ?_
    · rw [← franje]; apply shiny; intro L hl
      unfold buoy; rw [he]; have hh: (List.map (@bolt (Primary n G)) (x::L)).length≤ m+1:=by simp only [List.length_map,List.length_cons,hl,le_refl]
      rw [wed (m+1) _ _ _ (ContDiffAt.sum (fun i _=> ht i)) hh]; let v:=List.map (@bolt (Primary n G)) (x::L)
      have hx(t): roc (fun x=>∑ i∈Finset.range t,P i x) v 0= ∑ i∈Finset.range t,roc (P i) v 0:=by
          induction t with
          | zero=> simp only [Finset.range_zero,Finset.sum_empty]; simpa using Lis.wed (m+1) v (0:ℝ) (fun _=> (0:ℝ)) (x:=(0:W)) contDiffAt_const hh
          | succ t ih=> simp_rw [Finset.sum_range_succ]; rw [← ih]; apply Lis.addedL (m+1) v (fun x=>∑ i∈Finset.range t,P i x) (P t) (ContDiffAt.sum (fun i _=> ht i)) (ht t) hh
      rw [neg_one_mul, abs_neg,show roc (fun y=>∑ i∈ Finset.range r,P i y) _ _= _ from hx r,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by unfold tide; positivity)
    unfold statue; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i hi=>?_ ; have hh:= dots (X i) x s (hX _ (m+2)) (m:=m) le_rfl (hZ i (Finset.mem_range.mp hi)) hk hx (r-i); exact hh
omit hk hZ
local notation "r!"=> (4*100^3/(n.val:ℝ)^3)
variable (hC:∀ i< r,∀ y':Primary n G,∀ j,j≤3→Yarn j (fun L:List (Primary n G)=> |buoy (atlas S p i R l) 0 (y'::L)| *swipe (Measuring.chart n G) b v (y'::L))≤Z)(hp:6 ≤ v)
include hC hp
lemma annual (hY:Yarn 2 (fun T:List K=>|H r (x::T)| *Ch₀ (x::T)) ≤ Q) : Conde (target x) (r!*Q+fΣ 1*Z) 2 2 (fun l' => H r (x::l')):= by
    refine slope (X r) x 3 ((Cacao.vent ..).contDiffAt.of_le le_top) hx hp hY ?_ le_rfl
    exact fun i=> titled S R l x i hF hr (by omega) hx (fun r h s i he=> hC r h s i (by omega))
lemma quad (hY:Yarn 3 (fun T:List K=>|H r (x::T)| *Ch₀ (x::T)) ≤ Q): Conde (target x) (r!*Q+ fΣ 2*Z) 3 1 (fun l'=>H r (x::l')):= by
    refine angel (X r) x 4 ((Cacao.vent ..).contDiffAt.of_le le_top) hx hp hY (fun i=> titled S R l x i hF hr (p:=p) (b:=b) (v:=v) (by omega) hx (fun r h s i he=> hC r h s i he)) le_rfl
omit hC
-- certificate for tooth.Keeps. r≥1
lemma billy (t:G.ColorIndex)(hK:Keeps S p (sun G t))(hG:G.Simple)(h:r ≠ 0)(hQ:∀ i: Primary n G,Yarn 1 (fun T:List K=>|H r (i::T)| *Ch₀ (i::T)) ≤ Q): Conde (target x) (64*(0+100*tumbler n Q)) 1 3 (fun L=> H r (x::L)):=by
    have hz:grossH (rim (X r)) (sun G t)=0:=by
        apply Eq.trans _ (hK.sitting _ hr); unfold atlas; dsimp only; rw [show joy _ _ = joy S r from ?_]; rfl; unfold joy tariff; simp [PowerSeries.coeff_C_of_ne_zero h]
    let i:=rope x; have hh : Ribbon (rim (X r)):= ribbon (rim (X r)) S R l p r hF hG hr rfl
    have hx(L s)(hl:L.length <3):= candles (X r) ((Cacao.vent ..).contDiffAt.of_le le_top) hG t hh hx hp hQ x s L hl -- binder declaration `s` type inference
    intro L s he; have he:=hx L s he; unfold cost at he; rw [← Midpoint.close hh (sun G t) ,hz, abs_zero] at he -- inspect
    exact he
end YM.MSbar.Lis
