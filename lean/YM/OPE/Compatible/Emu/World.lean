import YM.OPE.Compatible.Emu.Poppy
/-!
# Origin reads. Work on constant finance type.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance
variable {i j d k m r l:ℕ}{n:Side}
local notation "EL" I=> Edge I
local notation "Y!"=> Keys G (Body 1 n)
variable (G)(hp:Board n (r+1))
noncomputable abbrev Chamber (G:Gauge)(r:ℕ):= Libra.Keys G (fieldP r)
noncomputable def arkE (e:EL (Site n)):Body 1 n:= (e.1,coord e.2)
lemma ark_sett (e:Edge Cover)(n:Side): sett n 0 e= arkE (Moor e n):=by simp only [sett,Variance.placed,zero_add]; rfl
lemma arkInj :Injective (arkE (n:=n)):= fun x y h=>Prod.ext (congrArg (fun x:Body 1 n=>x.1) h) (axisEquiv.injective (show axisEquiv x.2=axisEquiv y.2 from congrArg Prod.snd h))
lemma arkSur :Surjective (arkE (n:=n)):=by rintro ⟨i,j⟩; obtain ⟨p,rfl⟩:=axisEquiv.surjective j;exact ⟨(i,p),rfl⟩
noncomputable def dig (hp:Board n (r+1)): (fieldP r:Type) ↪ (EL (Site n)):= ⟨fun e=> Moor e.val n,fun x y he=>Subtype.ext (peers hp (mem_sdiff.mp x.property).1 (mem_sdiff.mp y.property).1 he)⟩
lemma ported (e:↥(fieldP r)): dig hp e∈fringe r n:= mem_image_of_mem _ e.property
lemma from_port (e:EL (Site n))(he:e∈fringe r n): ∃ x,dig hp x=e:=by obtain ⟨x,hx,h⟩:=mem_image.mp he; exact ⟨⟨x,hx⟩,h⟩
noncomputable def terr (hp:Board n (r+1)): ↥(fieldP r) ↪ Body 1 n:= (dig hp).trans ⟨arkE,arkInj⟩
noncomputable abbrev PinT:=dip (fun x:↥(fieldP r)=> x.val) n 0 (G:=G)
lemma PinS (x:Bid.Dir G n)(i:↥(fieldP r)):PinT G x i=x (terr hp i):=by
        change x (sett n 0 i.val)=_; rw [ark_sett]; rfl
noncomputable def sailT : Chamber G r →L[ℝ] Bid.Dir G n:= ContinuousLinearMap.pi fun i=> if h:∃ j,terr hp j=i then (ContinuousLinearMap.proj h.choose) else 0
lemma tide (x:Chamber G r)(i:↥(fieldP r)): sailT G hp x (terr hp i)=x i:=by
       unfold sailT;let v:=terr hp i; have hh: ∃ j,terr hp j=terr hp i:= ⟨i,rfl⟩; rw [ContinuousLinearMap.pi_apply,dif_pos hh,show hh.choose=i from (terr hp).injective hh.choose_spec]; rfl
lemma ave (x:Chamber G r): PinT G (sailT G hp x) =x:=funext fun i=> (PinS ..).trans (tide _ _ x i) -- unif
lemma silly (x:Chamber G r)(e:EL (Site n))(he:e∉fringe r n):sailT G hp x (arkE e)=0:=by
       unfold sailT; rw [ContinuousLinearMap.pi_apply,dif_neg]; rfl; rintro ⟨t,ht⟩; exact he (arkInj ht ▸ ported hp t) -- arrow
lemma arkL (x:Bid.Dir G n)(e:EL (Site n)):represent x e=G.lieExp (x (arkE e)):=by unfold represent increment arkE; rw[Pi.one_apply,mul_one]; rfl
lemma holeS (x:Chamber G r)(c:↥(fieldP r)):represent (sailT G hp x) (dig hp c)= G.lieExp (x c):=by rw[arkL,show arkE (dig hp c)=terr hp c from rfl, tide] -- unif
lemma zeroRing (x:Chamber G r)(e:EL (Site n))(he:e∉fringe r n): represent (sailT G hp x) e=1:=by rw[arkL,silly _ hp x e he, G.mat_lieExp_zero]
-- splitting: prj-map.R.
noncomputable def rejT : Bid.Dir G n→L[ℝ] Bid.Dir G n:= ContinuousLinearMap.id ℝ _- sailT G hp ∘L PinT G
lemma remT (x:Bid.Dir G n):x=rejT G hp x+sailT G hp (PinT G x):= by unfold rejT; simp
lemma remS (x:Bid.Dir G n):PinT G (rejT G hp x)= (0:Chamber G r):=by unfold rejT; rw [_root_.sub_apply, ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply, _root_.map_sub,ave,sub_self]
lemma silent (x:Chamber G r):rejT G hp (sailT G hp x)=0:=by unfold rejT; rw [_root_.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,ave,sub_self]
lemma rag (x:Bid.Dir G n)(e:EL (Site n))(he:e∉fringe r n): rejT G hp x (arkE e)=x (arkE e):=by
       nth_rw 2 [remT G hp x]; rw[Pi.add_apply,silly _ hp _ e he]; exact (add_zero _).symm -- occ
lemma rug (x:Bid.Dir G n)(j:↥(fieldP r)): rejT G hp x (arkE (dig hp j))=0:=by
       rw[show arkE (dig hp j)=terr hp j from rfl,← PinS G hp (rejT G hp x) j,remS]; rfl
lemma feltF (x y:Bid.Dir G n): rejT G hp x=rejT G hp y ↔ ∀ e, e∉fringe r n→ x (arkE e)=y (arkE e):=by
       refine ⟨fun H e he=>?_,fun H=>?_⟩
       · rw [← rag G hp x e he,← rag G hp y e he,H]
       have hz(i:Edge (Site n)): rejT G hp x (arkE i)=rejT G hp y (arkE i):=by
           by_cases h:i∈ fringe r n; swap;· exact (rag G hp x i h).trans ((H _ h).trans (rag G hp y i h).symm)
           obtain ⟨j,hj⟩:=from_port hp i h; subst i; rw[rug,rug]
       funext e; obtain ⟨i,hi⟩:= arkSur e; rw[← hi]; exact hz i
lemma ebbNorm (x:Chamber G r)(e:Edge (Site n)): ‖sailT G hp x (arkE e)‖ ≤ ‖x‖ :=by
       by_cases h:e∈fringe r n; swap;· rw[silly G hp x e h,norm_zero]; exact norm_nonneg _
       obtain ⟨j,hj⟩:=from_port hp e h; subst e; rw [show arkE (dig hp j)=terr hp j from rfl,tide G hp x j]; exact norm_le_pi_norm x j
-- sup without requiring period cutoff.Still need coercivity on Chamber.
end YM.OPE.Merchant
