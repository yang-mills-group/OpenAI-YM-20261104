import YM.OPE.Compatible.Emu.Frost
import YM.OPE.Compatible.Parch.Flint
/-!
# Mates. Occupancy localization. Generate linear gauge matching at all mesas.
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
open Drift Char Silt Silt.Float Module Variance StepsL Claw
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}
variable {D V:Type}
local notation "T!"=>Bid.Dir G n
local notation "F!"=>Body 1 n
variable (hp:Board n (r+1))
-- choose additive torque via recursion over berth.height
noncomputable def grit (x:Edge (Site n)→G.Color) (hp:Board n (r+1)) (y:Site n): G.Color:= if h:pdist y ≤ r then
      have H: vertQ r (y+step perch) < vertQ r y := (elevator hp y h) ▸ Nat.lt_succ_self _
      x (y,perch) + grit x hp (y+step perch)
      else 0
termination_by vertQ r y
lemma pity (x:Edge (Site n)→G.Color)(y:Site n)(h:r<pdist y): grit x hp y=0:=by rw[grit,dif_neg h.not_ge]
lemma paid (x:Edge (Site n)→G.Color)(y:Site n)(h:pdist y ≤ r): grit x hp y=x (y,perch) + grit x hp (y+step perch):=by rw[grit,dif_pos h]
include hp in lemma Hero (x:Edge (Site n)→ G.Color):∃ v: Site n→ G.Color,(∀ i,r<pdist i→ v i=0) ∧∀ i∈mesa r n, v i.1-v (dotUp i)=x i:=by
        refine ⟨grit x hp,(fun i hi=> pity hp x i hi),?_⟩; intro i hi; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; obtain ⟨t,ht,rfl⟩:=mem_image.mp hk; rw [show Moor _ _=(wrap n t,perch) from rfl]; exact sub_eq_iff_eq_add.mpr (paid hp _ _ (aery (tip hp (Nat.le_succ _)) ht))
variable {Y:Type}
lemma Rig (x y:T!) (f:T!→Y)(hh:∀ z v,f (z+sailT G hp v)=f z)(hf:rejT G hp x=rejT G hp y): f x=f y:=by
       rw [remT G hp x,remT G hp y,hh,hh,hf] -- h unused remove
lemma GateV (u:Site n→ G.Color)(x:Edge (Site n)):gillS (tor n) u (arkE x)= u x.1 - u (dotUp x):=by
       change u x.1-u (x.1+step (axisEquiv.symm (axisEquiv x.2)))=_; rw [Equiv.symm_apply_apply]
lemma melt (x y:T!) (f:T!→ℝ)(hh:∀ z v,f (z+sailT G hp v)=f z)(ht:LevelA (tor n) f)(hv:∀ i:Edge (Site n),i∉mesa r n→ i∉fringe r n→ x (arkE i)=y (arkE i)): f x=f y:=by
       obtain ⟨g,hg,h⟩:=Hero hp (fun i=>y (arkE i)- x (arkE i)); suffices H:f (x+gillS (tor n) g)=f y by rw [ht.tilts] at H; exact H
       apply Rig hp _ _ _ hh; rw [feltF]; intro i hi; rw [Pi.add_apply,GateV]; by_cases H:i∈mesa r n; · rw [h i H]; abel
       have he:(¬ pdist i.1 ≤ r)∧¬ pdist (dotUp i) ≤ r:=(not_or.mp (show ¬ (pdist i.1≤r ∨ pdist (dotUp i) ≤ r) from fun e=>?_)); swap;· exact ((regionH _ hp).mpr (e.imp (berthH _|>.mpr) (berthH _|>.mpr))).elim H hi
       rw [hg _ (not_le.mp he.1),hg _ (not_le.mp he.2), sub_self, add_zero,hv _ H hi]
-- support decouple. Ref budgets and Scroll surfaces.
variable (b)
structure Crisp (q:Finset (Edge Cover))(x:Bid.Dir G n→ Y): Prop where
       jury :∀ i j,BlurD G q n i=BlurD G q n j→ x i=x j
namespace Crisp
variable {f:Bid.Dir G n→ℝ}
lemma cull (hb:Board n b)(hv:r<b)(he: Crisp (bark b) f) (hp:Board n (r+1)) (h:∀ z v,f (z+sailT G hp v)=f z)(hh: LevelA (tor n) f): Crisp (leash r b) f:=by
        constructor; intro x y hx; let T:Finset (F!) := (bark b).image fun p=>arkE (Moor p n); let z:T!:=fun i=>if i∈ T then y i else x i
        refine Eq.trans ?_ (he.jury z y ?_); swap; · funext i;rw [echoP,echoP]; exact if_pos (show arkE _∈T from (mem_image_of_mem _ i.property))
        apply melt hp x z f h hh; intro i hi hp; unfold z; split_ifs with hs; swap; · rfl
        obtain ⟨j,hj,hS⟩:=mem_image.mp hs; have hT:= (arkInj (show arkE _=arkE i from hS)); have ht:j∉Delta r:=fun h=>?_ ; swap;· exact ((regionH i (tip hb (by omega))).mpr (hT ▸ qual (tip hb (by omega)) j h)).elim hi hp
        let k:↥(leash r b):= ⟨j,(tons j).2 ⟨hj, ht⟩⟩; rw [←hS]; rw [show x _=BlurD G (leash r b) n x k from (echoP ..).symm]; exact (congr_fun hx k).trans (echoP ..)
end Crisp
end YM.OPE.Merchant
