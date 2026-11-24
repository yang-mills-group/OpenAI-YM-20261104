import YM.OPE.Compatible.Channel.Force
/-! Page dimensions with orientations, push diagonal color
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix Exterior
open scoped Topology BigOperators Classical
variable {r n m:ℕ} {I J T:Type*} {L c f: Side}{α U:ℝ}
namespace Script
open Page
section items
def sliceP (p:Script T r)(i:Ink T r): Bin r→ℝ:= fun x=>p (syn x i)
def crop (p: Script T (r+1))(i: Ink T (r+1)) : Bin r→ℝ:= fun x=> sliceP p i (wreath r (0,x))
abbrev Bells (p:Script T r)(d:ℕ):Prop:=∀ i:Ink T r,purewell (sliceP p i) d
abbrev Poll (p:Script T (r+1))(d:ℕ):Prop:=∀ i:Ink T (r+1),purewell (crop p i) d
lemma slices {p: Script T r}(h:soot m p U) (a:Ink T r): Sack (poise m) (sliceP p a) U:=by
     let V :Bin r→Page T r:=fun i=> syn i a; have hv : Injective V:= fun i p h=> congr_arg Page.xy h
     let u (i):= figure m i*‖p i‖
     change SumBudget (u ∘ V) U; have he:= h.2.1.comp_injective hv
     refine ⟨fun i=>h.1 _,he,he.tsum_le_of_sum_le fun a=>?_⟩; apply le_trans _ (h.upto (Finset.image V a)); rw [Finset.sum_image]; exact le_rfl; exact hv.injOn
lemma crops {p:Script T (r+1)} (h:soot m p U)(a:Ink T (r+1)): Sack (poise m) (crop p a) U:=by
    let V(i:Bin r):= wreath r (0,i); have he:Injective V:=fun x y h=>congr_arg Prod.snd ((wreath r).injective h); have hx(i): poise m (V i)=poise m i:= by unfold poise; rw [plow]; --
    let u i:= poise m i*‖sliceP p a i‖; have hp:= slices h a; unfold Sack; simp_rw [show (fun x:Bin r=> poise m x*‖crop p a x‖)=u ∘ V from funext (fun i=> by rw [← hx i];rfl)]
    have hx:= hp.2.1.comp_injective he; refine ⟨fun i=>hp.1 _,hx,hx.tsum_le_of_sum_le fun a=>?_⟩; apply le_trans _ (hp.upto (Finset.image V a)); rw [Finset.sum_image]; exact le_rfl; exact he.injOn
lemma pin_slots (p: Script T (r+1))(a:Ink T (r+1))(x : Bin (r+1))(h: p.pinned): sliceP p a x=upland (crop p a) x:=by
   unfold upland; split
   next ht =>
      unfold crop; congr 1; rw [← ht]; exact ((wreath r).apply_symm_apply x).symm
   next ht => exact not_ne_iff.mp fun he => ht (h (syn x a) he)
-- accounting
lemma from_rows (p:Script T (r+1))(a:Ink T (r+1)):sliceP (silt p) a=upland (midland (sliceP p a)):=by
    ext x;unfold sliceP; unfold upland; split
    next ht=>
       unfold silt Sack.rope; -- fiber exact at (0,x). tsum via Injective compact
       let V(k:Cover) := syn (wreath r (k,riseZ x)) a
       have hp : stepOut x 0=0:= ht
       let q := syn x a
       have he(u:Cover): q=(Page.slide (-u) (V u)):= by
           funext i; refine Fin.cases ?_ (fun j=>?_) i; ext1
           · change stepOut x 0=-u+stepOut (wreath r (u,riseZ x)) 0; rw [hp,header,neg_add_cancel]
           · rfl
           ext1
           · have hv:= flowPart u (riseZ x) j
             change stepOut x j.succ=-u+stepOut (wreath r (u,riseZ x)) j.succ; rw [hv,neg_add_cancel_left]
             change _=stepOut x j.succ-stepOut x 0; rw [ht,sub_zero]
           rfl
       have hh(u:Cover) : steady (V u)=q:= by
          have hu:primary (V u)=u:= header ..; rw [steady,hu,← he]
       have hi:Injective V:=by intro i j H; exact (show i=_ from (header ..).symm).trans ((congr_arg primary H).trans (header ..))
       let g(y:Page T (r+1)):= if steady y=q then p y else 0
       calc
         (∑' i,g i)=∑' i,g (V i):= Eq.symm (hi.tsum_eq (f:=g) ?_)
         _ = _:= tsum_congr fun i=> by unfold g; rw [hh,if_pos rfl]
       intro y hy; refine ⟨primary y,?_⟩
       have hy': steady y=q:= Classical.byContradiction fun h=> hy (show g y=0 from if_neg h)
       apply (Page.slide (-primary y)).injective; rw [← he,← hy'];rfl
    next ht=> exact not_ne_iff.mp fun h=> ht ((rooted p) _ h)
end items
end Script
end YM.OPE.Flume
