import YM.OPE.Compatible.Blaze.Exit
/-! # Continuum orbit acts natural with script operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Prairies Woody Virgin Work.F08 Flume.Page Drift
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {n c f:Side}{G:Gauge}{C:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis) {τ:Phase→ℕ}
local notation "W"=> Tower (Shade G) d τ
local notation "W!"=> Tower (Shade G) d τ
lemma vivid (p: W!)(h:Aware d τ)(b:ℝ) : rebase G h b (Mirror a G d τ p)= Mirror a G d τ (rebase G h b p):=by
     refine bloomP _ _ _ (funext fun i=>funext (fun j=>?_)); set X:=p; rw [sunward]; change lilies _ _ _ (rebase _ _ _ _ i) _=shapeR a _ (lilies _ _ _ (rebase _ _ _ _ i) _); by_cases he:i=2; swap; · rw [sail _ _ h _ he,sail _ _ h _ he]; exact sunward ..
     subst i; rw [Drift.sip,Drift.sip,map_add,map_add,map_smul,map_smul,Pi.add_apply,Pi.add_apply,Pi.smul_apply,Pi.smul_apply,plusP,spay]; apply congr_arg₂ (·+·); exact sunward ..
     rw [peak_eq,peak_eq,spay]; congr 1; exact congr_arg ((j:ℝ) • ·) (sunward a p 0 j)
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{i:ℕ}{v u:ℝ}{b:ℝ}(A: Alps K T i v)(P':Patch)(U:Boxes G P' C)
lemma interposes (h: RollD A U P) (hp:Aware d τ)(p:solar G d τ): actor A U P b h hp (Mirror a G d τ p.val)=Mirror a G d τ (actor A U P b h hp p.val):=by
     let Ω:=actor A U P b h hp; let R:= Mirror a G d τ; let x:= Ω (R p.val); let y:=R (Ω p.val); let F:=Drift.spread G d τ
     have hk(n:Side)(u: Bid.Dir G n)(j:Phase):(inkM (F x) d 0 u).seq j.val=(inkM (F y) d 0 u).seq j.val:=by
         obtain ⟨V⟩:= mach P' C U A b h.eph h.flea n; let X(u:W!)(q:Site n)(v:Bid.Dir G n)(i:ℕ):= V.atW P q v i d j (F u); have he(w)(p:Site n)(u:Bid.Dir G n): Tendsto (X w p u) atTop (𝓝 ((inkM (F (Ω w)) d p u).seq j.val)):=by unfold F Ω; rw [offered b ..]; exact V.earns P u p j h.flea h.jar (m:=45) le_rfl _ _ (resin w (awareLeaf hp))
         rw [show inkM _ _ _ u= _ from (show inkM (F y) d 0 u= _ from toner a (Ω p.val) 0 u)]; apply tendsto_nhds_unique (he _ _ _); apply (he p.val _ _).congr'; filter_upwards with i; let m:=V.jet i; have hf: V.traceX i = V.traceX i:= rfl
         have hz:dart a (wrap m (lift (0:Site n)))=wrap m (lift (dart a (0:Site n))):=by simp [dart];
         have hh:= markerP a (subStud P' C (V.jet i)) P'.odd_side U (V.stems i) (V.accord i) (V.traceX i) h.jar p.val (wrap m (lift (0:Site n))) (Booklet (V.yarn i) G u); rw [ticketM a (V.yarn i),hz] at hh; exact congr_arg (fun t:Token=>t.seq j.val) hh
     have hx:x∈ solar G d τ:= actors b A U P h hp (R p.val) (solarMirror a p.val p.property)
     have hy:y∈ solar G d τ:=solarMirror a _ (actors b A U P h hp _ p.property)
     apply (bloomP G d τ); change F x=F y; funext j; apply scoreF (F x j) (F y j) (hp:=resin x (m:=0) (fun _=>by omega) j) (hq:=resin y (m:=0) (fun _=>by omega) j) (hx.1 j) (hy.1 j); intro n w; obtain ⟨u,rfl⟩:= (spool G n).surjective w; have ht:= hk n u j; rwa [vein_i,vein_i] at ht
-- constr
end YM.OPE.Quit
