import YM.OPE.Compatible.Jess.Suite
/-!
# Rebase invertible Ward α. automatic all B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
variable {K:Sponsor G}{T:Seasons K}{v u b:ℝ}
variable {P:Patch}{C:KernelChoices}(A:Alps K T i v)(U: Boxes G P C)(R:ChartRatio G)
variable (h:RollD A U R)(hp:Aware d τ)
include h hp
lemma Foz (p:T!)(V:Cola P C U A n b)(x: Site n)(y:Bid.Dir G n)(j:Phase): Tendsto (fun i=> V.atW R x y i d j (spread G d τ p)) atTop (𝓝 ((inkM (spread G d τ (actor A U R b h hp p)) d x y).seq j.val)):=by rw [offered]; exact V.earns R _ _ _ h.flea h.jar le_rfl _ _ (resin p (m:=45) (awareLeaf hp))
lemma FozJet (p:T!)(V:Cola P C U A n b)(x:Site n)(y:Bid.Dir G n) : Tendsto (fun i=> deriv (fun t:ℝ=> V.atW R x (t • y) i d 0 (spread G d τ p)) 1) atTop (𝓝 (deriv (fun t:ℝ=>(inkM (spread G d τ (actor A U R b h hp p)) d x (t • y)).s) 1)):=by
      obtain ⟨w,hw,H⟩:= liquidity P C U A R h.flea h.jar (show 1+44≤45 from by omega) (d:=d) b
      have ht:=resin p (m:=45) (awareLeaf hp); let X:=spread G d τ p; let D:=ContinuousLinearMap.toSpanSingleton ℝ y; let f (x:ℝ):=D x
      let q(s:ℝ):=(inkM (spread G d τ (actor A U R b h hp p)) d x (f s)).s; let z(i:ℕ)(t:ℝ):= V.atW R x (f t) i d 0 X
      change Tendsto (fun i=> deriv (z i) 1) _ (𝓝 (deriv q 1)); apply refresh z q _ _ (glideZ d) _ _ 1
      · intro i; let S:=subStud P C (V.jet i); let F:= V.traceX i; let a:=wrap (V.jet i) (lift x); let p :=TracePay S P.odd_side U A (V.stems i) (V.paths i) R d X b a F; have hA : ScriptJ.B p:=Fiber.predictB (F:=F.L) h.jar _ (fun j=> ((meridian _ _ _ _ _ ht) j).compLinear (ribz S P.odd_side).toLinearMap); exact (hA 0).compLinear (Booklet (V.yarn i) G ∘L D).toLinearMap
      · exact ((meridian _ _ 0 _ _ (resin _ (fun i=>Nat.zero_le _))) 0).compLinear D.toLinearMap
      · intro i; let n':= V.jet i; let p':=wrap n' (lift x); let F:=spool G n y; refine ⟨w*‖p‖*(‖F‖+1)^glideZ d,by positivity,fun v=> ?_⟩
        have H:= (H n' (V.light i) (V.paths i) (V.accord i) (V.stems i) (V.traceX i) p' X ‖p‖ ht) -- maybe implicit
        let M:=Booklet (V.yarn i) G; let B:=actor A U R b h hp; let W:=spread G d τ
        have hv: (trimT (V.jet i) n (V.yarn i)) p'=x:=(lease ..).trans (wrap_lift _); have ha:= H.2 (M (v • y)) 0; rw [←offered b A U R h p hp,show inkM _ _ _ (M _) =_ from (show inkM (W (B p)) d p' (M (v • y))= _ from labRel ..),hv] at ha; change ‖z i v-q v‖ ≤ _
        have hh: 1+‖spool G n' (M (v • y))‖ ≤ (‖F‖+1)*(1+‖v‖) := by apply le_trans (add_le_add_right (book_eq (V.yarn i) (v • y)) _); rw [map_smul,norm_smul]; change 1+‖v‖*‖F‖≤_; nlinarith only [norm_nonneg v, norm_nonneg F]
        apply (le_mul_of_one_le_left (norm_nonneg _) (grain_b (N:=n') 1)).trans; exact ha.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) (by positivity)).trans_eq (by rw [mul_pow, mul_assoc (w* ‖p‖)]))
      exact fun x=> Foz A U R h hp p V _ _ _ -- h
-- shift α+λ=χ
lemma works (x:T!)(a b:ℝ): actor A U R b h hp (rebase G hp (b-a) x) = rebase G hp (b-a) (actor A U R a h hp x):=by
      let p:=actor A U R a h hp x; let M:=spread G d τ; let q:=rebase G hp (b-a) p; let z:= rebase G hp (b-a) x; let v:= actor A U R b h hp z; apply bloomP G d τ; apply MsUnique (resin v (m:=45) (awareLeaf hp)) (resin q (m:=45) (awareLeaf hp)); -- need sorted of rebase raw without x sorted: actor sorted always. prove algebra.
      · change Rainbow (spread G d τ (actor A U R b h hp _)); rw [offered]; exact rainbow P C U A R _ b
      · have he:Rainbow (M p):=by unfold M p; rw [offered]; exact rainbow P C U A R _ a
        intro i j; change sorted (lilies (τ i) _ _ (q i) j); by_cases hp':i=2; swap; · unfold q; rw [sail _ _ _ _ hp']; exact he i j
        subst i; unfold q; rw [sip,map_add,map_smul,Pi.add_apply,Pi.smul_apply]; erw [peak_eq (d:=d)]; intro u
        change swing u (M p (2:Phase) j)+( (b-a)/2) • (j:ℝ) • swing u (M p (0:Phase) j)= _; rw [he 0 j u,he 2 j u]; rfl
      intro n u; obtain ⟨V⟩:= mach _ _ U A a h.eph h.flea n; let Z':Cola P C U A n b:= { V with traceX:= fun k=>Classical.choice (enrol _ _ _ _ (V.accord k) b h.flea) }
      let D:= ((b-a)/2)*deriv (fun i:ℝ=> (inkM (M p) d 0 (i • u)).s) 1
      rw [show inkM _ _ _ u= _ from (show inkM (M q) d 0 u= inkM (M p) d 0 u+ merry D from flot ..)] -- maybe direction ambiguous
      have he(k):= Foz A U R h hp x V 0 u k; have ht(k):= Foz A U R h hp z Z' 0 u k; let I(k:ℕ):= ((b-a)/2)*deriv (fun t:ℝ=>V.atW R 0 (t • u) k d 0 (M x)) 1; have hh:= (FozJet A U R h hp x V 0 u).const_mul ((b-a)/2)
      have hy(k:ℕ)(i): Z'.atW R 0 u k d i (M z)=V.atW R 0 u k d i (M x)+(merry (I k)).seq i.val:=by
           unfold Cola.atW; let S:= subStud P C (V.jet k); let a':=wrap (V.jet k) (lift (0:Site n)); let D':=Booklet (V.yarn k) G
           have hX:=star_base (K:=K) S P.odd_side U A R _ _ (V.accord k) h.jar h.flea (V.traceX k) (Z'.traceX k) x hp a' (D' u)
           have hY : TracePay S P.odd_side U A (V.stems k) (V.paths k) R d (M z) b a' (Z'.traceX k) (D' u)= _:= hX -- use lemma derivative
           erw [hY]; let f:= TracePay S P.odd_side U A (V.stems k) (V.paths k) R d (M x) a a' (V.traceX k)
           have ha(i:ℝ):(f (i • D' u)).s = V.atW R 0 (i • u) k d 0 (M x):=by rw [← map_smul];rfl
           have hk: (f (D' u)).seq i.val=V.atW R 0 u k d i (M x):=rfl; change (f (D' u)+merry (((b-a)/2)*deriv (fun i:ℝ=>(f (i • D' u)).s) 1)).seq _ = V.atW _ _ _ _ _ _ _+ _; rw [funext ha,← hk]; fin_cases i<;>rfl
      apply JetS.eta; · change _= (inkM _ _ _ _).s+(merry D).s; refine tendsto_nhds_unique_of_eventuallyEq (ht 0) ((he 0).add tendsto_const_nhds) (Eventually.of_forall fun i=> hy i 0)
      · change _= (inkM _ _ _ _).l+(merry D).l; refine tendsto_nhds_unique_of_eventuallyEq (ht 1) ((he 1).add tendsto_const_nhds) (Eventually.of_forall fun i=> hy i 1)
      change _= (inkM _ _ _ _).h + D; exact tendsto_nhds_unique_of_eventuallyEq (ht 2) ((he 2).add hh) (Eventually.of_forall fun i=> hy i 2)
end YM.OPE.Drift
