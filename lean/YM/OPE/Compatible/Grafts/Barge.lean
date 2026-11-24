import YM.OPE.Compatible.Grafts.Rum
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
variable (X:FibreRep S he U t A g b)
open Flume.Script Shell Char
open Planned.PrimaryIntegral295.Carrier
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
local notation "T!"=> Flume.Script.Tile G S.ratio.count
local notation "Uo"=> FUND S he U
def AzLight (G:Gauge) : AxisChart G X!→L[ℝ] deck (Script.Tile G S.ratio.count) c:= dance S he G ∘L ContinuousLinearMap.inr ℝ (Bid.Dir G c) (AxisChart G X!)
include X
lemma xiW (x y: Active G X!):
    Oriel X.L.Q (AzLight S he G) (pileV S he G x) (pileV S he G y)=Uo⁻¹ x y:=by
       let M:=X.L.Q; let A:= Uo; have hh:IsUnit A.det:= isUnit_iff_ne_zero.mpr (ulk_force S he U).det_pos.ne'; let C:= cash (countingBasis X! G); let F:=Ferry (AzLight S he G) ∘ pileV S he G; have hx(i q): F i q=C q i:= petalV S.ratio he ((0:K!),q) i; let u:= (A⁻¹)*ᵥ Pi.single y 1; let v:= C.symm u; have hv:C v=u:=C.apply_symm_apply _
       change M.wick (F x) (F y) =_; rw [wix_sym (Chart.tangent G (forest S.ratio he).Free) M (F x)]; change F x (M.inverse (F y))=_; have hy: M.P v= F y:= LinearMap.ext fun a=> by rw [M.turns,show M.P a v=_ from X.P0 a v]; change (C a ⬝ᵥ (A*ᵥ C v))= _; rw [hx,hv,show A*ᵥ u=Pi.single y 1 by unfold u;rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hh,Matrix.one_mulVec]]; simp
       rw [←hy,Law.solves,hx,hv]; simp [u,A]
include h t
lemma xial : Oriel X.L.Q (AzLight S he G)= (Piax S G U).acts c:=by
       let C:= X.L.Q; let x:= AzLight S he G; have ha(p:Tab (Shade G) c): Ferry x (starI p)=0:= LinearMap.ext fun i=>by change (spool G c) 0 p=0; simp
       ext i j; rcases pile_or S he i with ⟨p,rfl⟩|⟨p,rfl⟩
       · change C.wick (Ferry x _) (Ferry x _)=_; erw [ha,(piax_nil S U ..).1]; simp [Law.wick]
       rcases pile_or S he j with ⟨q,rfl⟩|⟨q,rfl⟩; · change C.wick (Ferry x (pileV S he G p)) (Ferry x (starI q))=_; erw [ha,(piax_nil S U ..).2]; simp [Law.wick]
       erw [planeR S he U t h,xiW S he U t X]
lemma scopeT (s B:ℝ)(hp:0<s)(hb:0≤B)(ht:U.dot.strip s B)(P:ChartRatio G) (x:deck T! c)(p: Site c)(m:ℕ) : Ribbon (mintR S A P b) (Piax S G U) (AzLight S he G) X.L.Q x p m (fun k:ℕ=> widthCost s k*B) 1:=by
       let P':= Piax S G U; let C:= X.L.Q; let V:= AzLight S he G; let b'(k):=widthCost s k*B; have h1(k): 0≤b' k:= mul_nonneg (zero_le_one.trans (widthCost_ge hp k)) hb; have hv : Oriel C V=P'.acts c:= xial S he U t h X
       constructor
       · constructor
         · refine ⟨h1 0,?_⟩;intro i; erw [hv]; rcases pile_or S he i with ⟨x,rfl⟩|⟨x,rfl⟩; · erw [show P'.acts c _ _=0 from (piax_nil S U ..).1,norm_zero]; exact h1 _
           erw [planeR S he U t h]; simpa only [Dux,pow_zero,one_mul] using! (payD S he U t h s ht hb hp 0).2 x x
         intro i _ j z; erw [hv,sub_self]; change _*‖(0:ℝ)‖≤ _; rw [norm_zero,mul_zero]; exact mul_nonneg (by unfold StepN; positivity) (h1 i)
       · norm_num
       intro i j b x ht u; erw [hv]; simp_rw [one_mul];rfl
-- Tilt v
lemma lytic (u:K!)(v:Z!):
      Fiber.drape K! Z! X.L.M (u,v)=fieldT (cabin g) u + (0,v):=by change (u,X.L.M u+v)=_; rw [X.M,folds t h.2.1]; exact Prod.ext (add_zero _).symm rfl
include ht
lemma expel (x:K!)(y:Z!)(hs:G.Simple):
      let T:=mintR S A P b
      let d:= Libra.Char.Sketch T 1 (dance S he G (fieldT (cabin g) x)) (AzLight S he G)
      Stell d y= X.L.cloth P (x,y):=by
           intro T d; let Q:=Fiber.drape K! Z! X.L.M (x,y); let B:= dance S he G;let P':=B (fieldT (cabin g) x); let C:= AzLight S he G; let V:=P'+C y; have hx:B Q= V:=by rw [show Q= _ from lytic S he U t h X x y,map_add];rfl
           change _=Adhesion.Curling _ _ Q
           rw [gumbar S he U t h ht X Q hs]; obtain ⟨h1,h2,h3⟩:=tide_feed S (A:=A) b P; have he'(i:Ask)(h:folk (Paloma T i)): d i y=library c (Paloma T i) (fun _=> B Q):=by
                 change (1:ℝ)*listV _ c (cue V P' 0 _)= _; erw [one_mul,muses _ (folk_whole h),hx]; congr! 1; funext i; unfold cue; rw [if_pos]; have h:=i.isLt; omega
           unfold Stell brat; rw [he' 0 h2, Pi.add_apply,he' 2 h3,he' 3 h1]; erw [beam2 S he U t h ht Q b,beam3 S he U t h Q,beam4 S he U t h Q]
end YM.OPE.Cascade.Rill
