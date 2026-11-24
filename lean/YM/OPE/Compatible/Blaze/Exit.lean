import YM.OPE.Compatible.Blaze.Act
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
local notation "Y"=> streak a G
lemma h_track (p q:ℝ→Bid.Dir G n) (s:ℝ→Site n→G.El) (h:(tor n).Track p q s): (tor n).Track (Y n ∘ p) (Y n∘ q) (fun x=>s x∘ dart a):=by
    let T:=streak a G n; refine ⟨(ContinuousLinearMap.contDiff ..).contDiffAt.comp _ h.hX,(ContinuousLinearMap.contDiff ..).contDiffAt.comp _ h.hY,?_,?_,?_,fun i=> h.chart _⟩; rw [Function.comp_apply,h.gx,map_zero];rw [Function.comp_apply,h.gy,map_zero]; filter_upwards [h.law] with i hi; rw [Mar_ord]; unfold Function.comp; rw [streak,rep_shifts,rep_shifts,show (fun x=> s i (dart a x))=(s i∘ affine (Wm a) (0:Site n)) from funext fun i=>by simp [dart,affine,Function.comp_apply],← pullGauge,Mar_ord _ _ _|>.1 hi] -- comp act unfold beware
lemma solarMirror (A: W)(h:A∈solar G d τ): Mirror a G d τ A∈ solar G d τ:=by
     let p:= Mirror a G _ _ A; refine ⟨sunherd a A h.1, fun n x=>?_⟩; let U:= inkM (spread G d τ A) d (dart a x); have hp:(tor n).Marbles U:=h.2 ..
     rw [show inkM _ _ x= U∘(Y n) from funext fun y=> toner a A x y]; refine ⟨fun i=> (hp.toll i).compLinear (streak a G n).toLinearMap,fun {p q s} hx=>?_⟩; apply (hp.honors (h_track a p q s hx)).congr' _ EventuallyEq.rfl; filter_upwards with i; change _ = ((U ((Y n) _)).atK i - (U ((Y n) _)).atK i); rw [map_smul,map_smul]; rfl
lemma ticketM (h:c.val∣n.val)(x:Bid.Dir G c): Y n (Booklet h G x)=Booklet h G (Y c x):=by
      let L:=trimT n c h; ext1 i; rcases i with ⟨j,i⟩; obtain ⟨i,rfl⟩:= axisEquiv.surjective i; change Y n _ (j,Exterior.coord i)= Y c _ (L j,Exterior.coord i); simp_rw [α_line]; have he:L ((Wm a).act j)=(Wm a).act (L j):=by nth_rw 1 [←wrap_lift j]; rw [wrap_signed, show L _= _ from lease _ _,←wrap_signed]; apply congr_arg; rw [← show L _= _ from (show L (wrap n (lift j))=wrap c (lift j) from lease ..),wrap_lift]
      have hv:L (dust a i)=dust a i:=by rw [fog_m, show L _= _ from lease _ _,← fog_m]
      split <;> first | apply congr_arg Neg.neg; change x (L (_+_),_)=_; rw [map_add,he,hv] | change x (L (_+_),_)=_; rw [map_add,he,hv]
variable {K:Sponsor G}{T:Seasons K}{i:ℕ}{v u:ℝ}{b:ℝ}{A: Alps K T i v}
attribute [local instance] Gauge.frobInner
variable (S:StepData c f) (H':Odd S.ratio.count.val)
local notation "Fr"=> forest S.ratio H'
lemma markerP (D:Boxes G S.patch S.kernel) (t:S.Choices){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→ AxisChart G Fr}(h:licensed S H' D A.clip A.live L A.sky g)(X:FibreRep S H' D t A g b)(p:LocalRatio P)(z: W) (x:Site c)(v:Bid.Dir G c):
     TracePay S H' D A t g P d (spread G d τ z) b (dart a x) X (streak a G c v)= TracePay S H' D A t g P d (spread G d τ (Mirror a G d τ z)) b x X v:=by
         unfold TracePay; let U:= spread G d τ z; let M:=inkM U d (S.ratio.embed (dart a x)); let K:= ribz S H' (G:=G); let Q:=M ∘ K; have hh:ScriptJ.B M:=meridian _ _ 0 _ _ (resin z (fun i=>Nat.zero_le _)); rw [PrizeTurn a S H' D t X h p Q (fun i=> (hh i).compLinear K.toLinearMap) v]; apply congr_arg (fun q=>X.L.predicts P q v)
         funext w; change M (K (Zig a S H' w))= _; have hz: dart a (S.ratio.embed x)=S.ratio.embed (dart a x):= Eq.symm (S.ratio.signed ..); rw [show K (Zig a S H' w)= _ from (show _=_ from (show K (Zig a S H' w)=streak a G f (K w) from DFunLike.congr_fun (Ziggle (G:=G) a S H') w))]; unfold M; rw [←hz]; exact (toner a z (S.ratio.embed x) (K w)).symm
end YM.OPE.Quit
