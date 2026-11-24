import YM.OPE.Compatible.Ibis.Bill
/-! # reading Sip orders of retargeted budget projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section
noncomputable def Ripple (G:Gauge)(h:Aware d τ)(t:ℝ) : solar G d τ→L[ℝ] solar G d τ:= let T:=trellisA G h; T ∘L T+t • T+t^2 • ContinuousLinearMap.id ℝ _
lemma twig (p:solar G d τ)(h:Aware d τ)(t:ℝ): Ripple G h t p= let T:= trellisA G h; T (T p)+ t • T p+t^2 • p:=rfl
noncomputable abbrev Goan (p:solar G d τ):= spread G d τ p.val
local notation "W'"=>solar G d τ
lemma finch (b:W')(h:Aware d τ)(hs:Tide (Goan b) d m r):Tide (Goan (trellisA G h b)) d m r:=by
        let P:=trellisA G h b; have hp:=hs; unfold Tide; intro i; have hr:=Sack.coins ((hs 0).2 0); by_cases hi:i.val=0
        · have hv : i=0:= Fin.ext hi
          rw [hv]; change Volume (lilies (τ 0) _ _ (Candy G h b.val 0)) _ _ _; rw [pal h _ _ (by decide), map_zero]; refine ⟨fun i hi=>rfl,fun i=> Sack.zero hr _⟩
        let j:Phase:=⟨i.val-1,by have h:=i.isLt;omega⟩; have ht:i.val=j.val+1:=by change i.val=(i.val-1)+1; omega
        change Volume (lilies _ _ _ (Candy G h b.val i)) (d+i.val) _ _; rw [glee _ _ i j ht, armL]; exact (hs j).raise _ (by omega) le_rfl -- linter arg?
lemma glowsC (b:ℝ)(p:solar G d τ)(ht:Tide (Goan p) d m t): Tide (Goan (b • p)) d m (‖b‖*t):=by intro i; change Volume (Drift.spread G d τ (b • p.val) i) _ _ _; rw [map_smul]; exact Volume.spread _ _ (ht i)
lemma glowsA (p q:solar G d τ)(h:Tide (Goan p) d m t)(he:Tide (Goan q) d m r):Tide (Goan (p+q)) d m (t+r):=by intro i; change Volume (Drift.spread G d τ (p.val+q.val) i) _ _ _; rw [map_add]; exact Volume.add _ (h i) (he i)
noncomputable abbrev earpE (t v:ℝ):= v + ‖t‖*v+‖t^2‖*v
lemma Uscrew (h:Aware d τ)(p:solar G d τ)(hs:Tide (Goan p) d m r): Tide (Goan (Ripple G h t p)) d m (earpE t r):=by
       rw [twig]; exact glowsA _ _ (glowsA _ _ (finch _ h (finch p h hs)) (glowsC _ _ (finch p h hs))) (glowsC _ _ hs)
variable (x:Site n) (p:solar G d τ)
lemma Rip_w (h:Aware d τ)(v:Bid.Dir G n): inkM (Goan (Ripple G h t p)) d x v= let z:= inkM (Goan p) d x v; Ū*(Ū*z) + JetS.plainJ t*(Ū*z)+JetS.plainJ (t^2)*z:=by
       let T:=trellisA G h; let R(p:solar G d τ):= inkM (Goan p) d x v; have he(x):R (T x)=Ū* R x:= congr_fun (Speel h x.val _) v; have ht(p q:solar G d τ): R (p+q)=R p+R q:=by unfold R Goan; erw [map_add]; exact Ink_sum _ _ _ _ d _ _ (resin p.val (m:=0) (fun _=>Nat.zero_le _)) (resin q.val (m:=0) (fun _=>Nat.zero_le _))
       have hx(p:solar G d τ)(z:ℝ):R (z • p)= JetS.plainJ z * R p:=by unfold R Goan;erw [map_smul]; exact Ink_scale ..
       change R (T (T p)+ t • T p+t^2 • p)=_; rw[ht,ht,hx,hx,he,he]
abbrev Rink (j:Phase):= LightP x (m:=τ j) (p.val j)
lemma Rinkq (j:Phase):skry (inkM (Goan p) d x) j=Rink x p j:=levelT ..
noncomputable abbrev Aview (p:solar G d τ)(x:Site n)(t:ℝ): Bid.Dir G n→ℝ:= fun i=>(inkM (Goan p) d x i).atK t
lemma HotC (h:Aware d τ):
       let q:= Ripple G h t p; let g:= Rink x q; let f:= Rink x p; g 2=Aview p x t ∧ g 1=t • g 2 - t^3 • f 2∧ g 0=t • g 1 - t^3 • f 1:=by
             intro q g f; have hh(i):g i=skry (inkM (Goan q) d x) i:= (Rinkq ..).symm; have he(i):f i= skry (inkM (Goan p) d x) i:= (Rinkq ..).symm; rw [hh 0,hh 1,hh 2,he 2,he 1]; let z(i):= inkM (Goan p) d x i
             have hx (i:Bid.Dir G n): inkM (Goan q) d x i= _:= Rip_w x p h (t:=t) _ -- ensure expression
             refine ⟨funext (fun i=>?_ ), funext (fun i=>?_ ), funext (fun i=>?_ )⟩; all_goals simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Aview,skry,JetS.atK,hx]; all_goals simp [JetS.seq,Ū]; all_goals ring
end
end YM.OPE.Ibis
