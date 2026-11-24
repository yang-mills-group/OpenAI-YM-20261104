import YM.OPE.Compatible.Channel.Mop
/-!
# Outputs interpreted at origin, all kernels. Also grants before-L costs backwards when activation fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix Exterior
open scoped Topology BigOperators Classical
variable {r n m j k:ℕ}{L c f:Side}{η U v:ℝ}
namespace Script
open Page
variable {W T:Type*}[Fintype W] [Fintype T]
omit [Fintype T]
lemma wordAll (A:Cross L T W)(h:Whole A)(p:Script T r)(y:Cover)(hp:Summable p): Summable (countermove A y p):=by
    obtain ⟨σ,C,hσ,hB⟩:=h
    apply sootS (counterflow hB hσ p y (show soot 0 p (∑' i,‖p i‖) from ?_)); unfold soot Page.figure poise Sack; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,hp.norm,le_rfl⟩
lemma VolAll (A:Cross L T W)(h:Whole A)(p:Script T r)(hp:Summable p): Summable (payVolume A p):=by
    let v(i:Site L):= countermove A (lift i) p; have hx(i:Site L): Summable (silt (v i)) :=by
       have hs := wordAll A h p (lift i) hp
       apply sootS (silt_cost (show soot 0 (v i) (∑' j,‖v i j‖) from ?_)); unfold soot Page.figure poise Sack; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _, hs.norm,le_rfl⟩
    rw [show payVolume A p=(fun x=>∑ i,silt (v i) x) from funext fun x=> Finset.sum_apply ..]; exact summable_sum (fun i _=> hx i)
private lemma totalLedger (p: Script T r)(hp:Summable p)(q: Script T r)(h:Summable q)
   (H:∀ n:Side,∀ w: Fin r→deck T n,scribe (0:Site n) p w=scribe 0 q w): p=q:=by
    let v (i:ℕ):Side:=⟨i+1,Nat.succ_pos i⟩; have hv:Tendsto (fun i=>(v i).val) atTop atTop:= tendsto_add_atTop_nat 1
    ext1 x; exact tendsto_nhds_unique_of_eventuallyEq (lands p hp x v hv) (lands q h x v hv) (Eventually.of_forall fun i:ℕ=> H _ _)
lemma territory (p: Script T r)(t:Cover)(hp:Summable p)(A:Cross L T W)(h:Whole A)(hs: sorted p): sorted (countermove A t p):=by
   intro i; let q:=countermove A t p; have ht:=wordAll A h p t hp; apply totalLedger _ (swing_sum q ht i) q ht
   intro n w; let f:=n*L; let g: Ratio n f:=⟨L,rfl⟩; rw [rotating]
   change scribe (0:Site n) (countermove (L:=g.count) A _ _) _=scribe _ (countermove (L:=g.count) A _ _) _; rw [bridge_torque (g:=g) h _ t p hp, bridge_torque (g:=g) h _ t p hp];
   let u j:= installed g A *ᵥ w j; change scribe _ p (u ∘ i)= _; rw [← rotating,hs]
private lemma volBook (p: Script T (r+1))(h:pinned p)(hp:Summable p)(q: Script T (r+1))(hq:pinned q)(u:Summable q)
   (H:∀ n:Side,∀ w:Fin (r+1)→deck T n,library n p w= library n q w): p=q:=by
    let v (i:ℕ):Side:=⟨i+1,Nat.succ_pos i⟩; have hv:Tendsto (fun i=>(v i).val) atTop atTop:= tendsto_add_atTop_nat 1
    ext1 x; by_cases he: x.primary=0; swap
    · rw [show p x=0 from not_ne_iff.mp fun g=> he (h _ g), show q x=0 from not_ne_iff.mp fun g=> he (hq _ g)]
    refine tendsto_nhds_unique_of_eventuallyEq (lands p hp x v hv) (lands q u x v hv) (Eventually.of_forall fun i:ℕ=> ?_); exact (centerSync p h he _).symm.trans ((H (v i) _).trans (centerSync q hq he _))
lemma tribal [Fintype T] (p:Script T (r+1))(hp:Summable p)(A:Cross L T W)(h:Whole A)(hX:p.Idem): (payVolume A p).Idem:=by
    let q:=payVolume A p; have hs:Summable q:= VolAll A h p hp; have hg: q.pinned:=by
       intro v hv; by_contra hy; apply hv; unfold q payVolume; rw [Finset.sum_apply]; exact sum_eq_zero fun i _=> not_ne_iff.mp (fun hh=> hy ((rooted _) v hh))
    refine ⟨hg,fun a=>?_⟩; have hx:= swing_sum q hs a; refine volBook (silt (swing a q)) (rooted _) ?_ q hg hs (fun n w=> ?_)
    · apply sootS (silt_cost (m:=0) (c:=(∑' i,‖swing a q i‖)) _); unfold soot Sack Page.figure poise; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,hx.norm,le_rfl⟩
    rw [← silt_read hx w, show library n (swing a q) w=library n q (w ∘ a) from Finset.sum_congr rfl (fun i _=>rotating ..)]; let f:=n*L; let g:Ratio n f:=⟨L,rfl⟩; let y i:=installed g A *ᵥ w i; unfold q; rw [volume_torque (g:=g) h p hp, volume_torque (g:=g) h p hp]
    change library f p (y ∘ a)=library f p y; calc
       _ =library f (swing a p) y:= Finset.sum_congr rfl fun i _=> (rotating ..).symm
       _ = library f (silt (swing a p)) y:= silt_read (swing_sum p hp a) _
       _ = _:=by rw [hX.2 a]
end Script
end YM.OPE.Flume
