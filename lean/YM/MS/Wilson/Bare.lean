import YM.MS.Wilson.Draft
/-!
# Stencils for the action and master test

Unscaled action at analytic level. Free and higher radiative parts from masks
 afterwards. Recapture exact translated identity on torus. Fourier relation after taps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Draft
open Function Filter Finset Set Plane Koszul Cylinder Taylor Lab Sew Chart Lattice Bare Focus
open Landau
open scoped Topology ContDiff
variable {G: Gauge}{P Q:Type} [AddCommGroup P] [AddCommGroup Q]

-- Wilson term with zero unimportant density. origin event.
def weightW (G:Gauge)(d:Rail P)(x:P): Dot G P:= ∑ k:PlaqAxes,Sew.art (loadC d (x,k)) gone
def weightH (G:Gauge)(x:P): Dot G P:= ∑ i:Axis,onedge (x,i) Maurer.lac

def ropes (G:Gauge)(d:Rail P)(x:P): Dot G P:= (∑ b:Axis,∑ i:Conn G,couple DotFlip (AHplus i (x,b)) (throat d (x,b) i))-
   ∑ i:Conn G, couple DotFlip (GHplus i x) (cog x i)
def bosons (G:Gauge)(d:Rail P)(x:P):=weightW G d x+ ropes G d x

section t
variable (G) (r:P→Q) {d:Rail P}{g:Rail Q}(h:∀ i k,r (i+d k)=r i+g k)
include h
lemma sweater (x:P): transport r (weightW G d x)= weightW G g (r x):= by
    simp_rw [weightW,map_sum,map_sec]; apply Finset.sum_congr rfl; intro i hi; congr 1; funext i; fin_cases i <;> simp [thread,loadC,h]
lemma sail_rope (x:P): transport r (ropes G d x)=ropes G g (r x):= by
    simp_rw [ropes,map_sub,map_sum,transport_comes,move_AH, move_GHplus,move_cog,throat,map_add,move_steer]; simp only [endRail,h]
lemma az_t (x:P): transport r (bosons G d x)=bosons G g (r x):=by simp only [bosons,map_add, sweater G r h, sail_rope G r h]
omit h [AddCommGroup P] [AddCommGroup Q] in
lemma sweaterH (x:P): transport r (weightH G x)=weightH G (r x):= by simp_rw [weightH,map_sum,onmove]
end t
section finite
variable (G) [Fintype P][DecidableEq P](d:Rail P)
-- sums all centers = finite definitions. Rent unambiguous use Chart.rent.
local notation "Y" => (glow G P) -- shadow issue
local notation "C"=> panel G P
lemma allWeight : (sumHome (weightW G d 0)).val= ink (Y).e0 (Chart.rent d):= by
   let F (x:Rout P):= gone (G:=G) ∘ (Sew.pull (loadC d x));
   have he (x:P): Lab.Shift x (weightW G d 0)=weightW G d x:= by rw [show Lab.Shift x (weightW G d 0)= weightW G d (x+0) from sweater G (fun i:P=>x+i) (fun _ _=> (add_assoc ..).symm) 0]; simp
   rw [total_uses]; simp_rw [he,weightW,sum_stack,pooled _ bill_gone]
   have hf (x:Rout P): germ (F x):= by
       let T : City G P →L[ℝ] Lot G Axis:= Sew.pull (loadC d x); have hx : ContDiffAt ℝ ω gone (T 0):= by rw [map_zero]; exact bill_gone
       exact hx.comp (f:=T) 0 T.contDiff.contDiffAt
   rw [show Chart.rent (G:=G) d=∑ k:Rout P,F k from funext fun x=> by rw [Finset.sum_apply]; rfl, ink_sum _ _ (fun i _=> hf _),Fintype.sum_prod_type]; rfl
lemma allRopes : (sumHome (ropes G d 0)).val=(Paper G P).hung (launch Y (colorTerm G P) (loco d)):= by
    have he (x:P): Lab.Shift x (ropes G d 0)= ropes G d x:= by rw [show Lab.Shift x (ropes G d 0)= ropes G d (x+0) from sail_rope G (fun i:P=>x+i) (fun _ _=> (add_assoc ..).symm) 0]; simp
    rw [total_uses]; simp_rw [he]; unfold Bonded.hung; rw [(C).split_i]; simp only [feeA,one_smul,feeK,neg_smul,← throat_frame d, ← cog_frame d] -- instantiate casts
    simp_rw [Fintype.sum_prod_type]; simp only [ropes, Finset.sum_sub_distrib,Submodule.coe_sub,sum_stack, ← sub_eq_add_neg, Finset.sum_neg_distrib]; rfl
lemma allH : (sumHome (weightH G (0:P))).val= ink (Y).e0 totalH:= by
    let F (x:Edge P):= (fun a:City G P=> Maurer.lac (a x));
    have he (x:P): Lab.Shift x (weightH G (0:P))=weightH G x:= by rw [show Lab.Shift x (weightH G (0:P))= weightH G (x+0) from sweaterH G (fun i:P=>x+i) 0]; simp
    rw [total_uses]; simp_rw [he,weightH,sum_stack,edge_parse _ (Maurer.hlog _)]
    have hf x : germ (F x):=(Maurer.hlog G).comp (f:=fun a:City G P =>a x) 0 (contDiff_apply ..|>.contDiffAt)
    rw [show totalH (G:=G) (P:=P)=∑ i: Edge P,F i by ext a; rw [Finset.sum_apply]; rfl,ink_sum _ _ (fun i _=> hf _),Fintype.sum_prod_type]; rfl
lemma source (G:Gauge) (d:Rail P) : (sumHome (bosons G d 0)).val=Sourced (Chart.rent d) (colorTerm G P) (loco d) (glow G P):= by
    simp only [Sourced,bosons,map_add,add_stack,allWeight,allRopes]
end finite
end YM.MS.Native.Draft
