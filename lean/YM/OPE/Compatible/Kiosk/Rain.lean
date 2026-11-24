import YM.OPE.Compatible.Kiosk.Will
/-!
# Credit on the unit coefficient, no additive drift in α comparisons at common post clip. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}{V:ChartRatio G}{p:Clip}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes Roles
def Penny (H:Seasons B)(P:Patch)(p:Clip)(V:ChartRatio G)(C:ℝ) (f:TileC H P p V C →ℝ):Prop:=∃ c:ℝ,0 ≤ c∧∃ n:ℕ,∀ i, ‖f i‖ ≤ c*upperX i ^ n * downK i
abbrev nightsF (r:ℕ) (i:TileC H P p V C):= (UA i).liftZ r
abbrev nightsV (r:ℕ) (i:TileC H P p V C):= (VA i).liftZ r
abbrev Newton (r:ℕ) (i:TileC H P p V C):= nightsF r i-nightsV r i
abbrev driftQ (i:TileC H P p V C):= betaA i • dayU 2 (fallsF i)-betaE i • dayV 2 (fallsF i)
abbrev bramble (i:TileC H P p V C):= flagsH P (Newton 2) i
abbrev yesterday (i:TileC H P p V C):= Newton 2 (fallsF i)+ driftQ i- bramble i
lemma folkNight (k:TileC H P p V C): folk (Newton r k):= folkD (((UA k).fullL r).here _) (((VA k).fullL r).here _)
lemma phosphorus (i:TileC H P p V C)(_h:3 ≤ m)(k:G.ColorIndex): costWorld k (0:Axis) (1:Axis) (yesterday i)= (-2:ℝ) * (betaA i-betaE i) :=by
    let v:=fallsF i; let Ux:= Newton 2 (fallsF i); let W:=costWorld k (0:Axis) (1:Axis); have hx (x:TileC H P p V C): Poll (Newton 2 x) 3:= Poll_diff _ _ (pollbb (UA x) (n:=1) (by omega)) (pollbb (VA x) (n:=1) (by omega)) (((UA x).fullL 2).here _) (((VA x).fullL 2).here _)
    have ha:=world_low k (0:Axis) (1:Axis) _ (hx v); have he: pinned (Newton 2 i):=((stint_cut _ _ _ _ ((UA i).fullL 2) ((VA i).fullL 2)).sym 2).1; have he:=comb_poll (hx i) (folkNight i) he (ship P (UA i).gear) (show 3≤P.J from le_trans (by decide) P.order_cut) B.K.penalty_pos P.order_cut
    let s:= (UA v); let t:= (VA v); have hs:=folkS ((s.fullK 2).here 2) (betaA i); have ht:=folkS ((t.fullK 2).here 2) (betaE i); erw [yesterday,wdep k (0:Axis) (1:Axis) (folkF (folkNight v) (folkD hs ht)) (show folk (bramble i) from displayP (folkNight i)),world_low k _ _ _ he,wcount k _ _ (folkNight v) (folkD hs ht)]; change W (Newton _ v)+(costWorld k _ _ _)-0 = _; erw [show W (Newton _ v)=0 from ha,wdep k _ _ hs ht, wscale k _ _ (s.word 2), wscale k _ _ (t.word 2),s.coinWhat k (0:Axis) (1:Axis) (by decide) P.order_cut,t.coinWhat k (0:Axis) (1:Axis) (by decide) P.order_cut]; ring
section
variable {T: Medal P G B.K P.J}(B0: Roles (M:=TileC H P p V C) T UA VA s downK upperX)
include B0
lemma tempo (h:G.Simple)(hv: LocalRatio V)(he: Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) 3 m)(hp: Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) 4 m): Wcap H P p V C m yesterday:=by
    let D(i:TileC H P p V C):= stitch (player (tourP T i) (nightsF 2 i))-stitch (player (tourV T i) (nightsV 2 i)) -bramble i; let F(i:TileC H P p V C):=(tourP T i).Hort (UA i).live (UA i).clip V - (tourV T i).Hort (VA i).live (VA i).clip V; have ht: Wcap H P p V C m D:=by
        refine B0.pager (r:=1) (p:=fun i=>(UA i).liftZ) (q:=fun i=>(VA i).liftZ) (fun i=>((UA i).fullL 2).here _) (fun i=>((VA i).fullL 2).here _) (LeafLoan ..).2 (fun i=>⟨_, stint_cut _ _ _ _ ((UA i).fullL 2) ((VA i).fullL 2)⟩) ?_
        intro i hi hy; obtain rfl:i=1:=by omega
        rw [show (fun j:TileC H P p V C=> ((fun i:TileC H P p V C=>(UA i).liftZ)-(fun i: TileC H P p V C=>(VA i).liftZ)) j 1)= _ from ?_]; exact Loan.zero m 1
        ext1 j; change (UA j).liftZ 1-(VA j).liftZ 1=(0:Script (Shade G) 1); erw [(UA j).soft_leaf h,(VA j).soft_leaf h]; abel
    rw [show yesterday (H:=H) (P:=P) (C:=C) (p:=p) (V:=V)= D+F from ?_]; exact Loan.seize ht (HortPay B0 V he hp) B0.fuel (fun i=>(B0.tune i).le)
    ext1 i; let v:=fallsF i; let X:=tourP T i; let Q:=tourV T i; have hA:= colorshift P T (UA i) _ (i.1.1.shot _) hv; have hB:=colorshift P T (VA i) _ (i.1.2.shot _) hv; let a:= UA i; let b:= VA i; have hh: nightsF 2 v+ betaA i • dayU 2 v=stitch (X.talo a.live a.clip V):= hA.2.2; have hQ:nightsV 2 v +betaE i • dayV 2 v=stitch (Q.talo b.live b.clip V):=hB.2.2; unfold yesterday driftQ Newton; rw [sub_add_sub_comm,hh,hQ,X.T2split a.pays,Q.T2split b.pays]; change (stitch (player X _)+X.Hort a.live a.clip V - (stitch (player Q _)+Q.Hort b.live b.clip V))-_=(stitch (player X _)-stitch (player Q _)-_)+(X.Hort a.live a.clip V-Q.Hort b.live b.clip V); abel
omit B0 in
lemma centaur (h:G.Simple)(hy:3≤m)(ht:Wcap H P p V C m yesterday): Penny H P p V C (betaA-betaE):=by
    obtain ⟨k⟩:=colorAvail G h; obtain ⟨x,h,K,H⟩:=ht; refine ⟨x,h,K,fun i=>?_⟩; have hp:=world_budget k (0:Axis) (1:Axis) (le_trans (by decide) hy) _ (H i); rw [phosphorus i hy k,norm_mul, norm_neg] at hp; norm_num at hp; exact le_trans (show ‖betaA i-betaE i‖≤2*‖betaA i-betaE i‖ by have hh:=norm_nonneg (betaA i-betaE i); linarith) hp
end
end Alps
end YM.OPE.Votive
