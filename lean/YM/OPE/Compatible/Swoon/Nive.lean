import YM.OPE.Compatible.Swoon.Harpo
/-!
# rho1 piece buy and cancellations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ" => Chart.tangent G Qµ
variable {C:Law  (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
abbrev πV (A:Alps K T i v)(n:ℕ):= (4:ℝ)⁻¹ • iteratedFDeriv ℝ n (pane X! t A.clip A.live) 0
include S he G g A L K U h t H C hc
lemma kin_c (jv:G.El)(x y:J!): C.P (glint _ jv x) (glint _ jv y)=C.P x y:=by
    rw [hc,hc,←tollY S he U h t,← tollY S he U h t]; let p:=InV S he H G; let q:=Busk S he jv; let z:=glint Qµ jv; let W:=iteratedFDeriv ℝ 2 (pane X! t A.clip A.live) 0
    have hp: ![p (z x),p (z y)]=q ∘ ![p x,p y]:=funext fun i=>by fin_cases i <;> exact (Buske S he H jv _).symm
    change W ![p _,p _]/4=W ![p _,p _]/4; rw [hp];exact congr_arg (fun x:ℝ=> x/4) (stillZ S he U t h ..)
lemma τFlat (hs:G.Simple)(x: Keys G (Limb H)): C.average Wμ (τ2 (πV S he t A 3) (fieldT (cabin g) (cloak H x)) (InV S he H G))=0:=by
      let p:= InV S he H G; let X:=fieldT (cabin g) (cloak H x); let Q:=πV S he t A 3; let T:= (fderiv ℝ (viewS (cabin g)) 0) ∘L cloak H; let Y(x):=τ2 Q (T x) p; have hp(x): Bond (Y x):= (τBond Q (T x) p).1
      let M : Keys G (Limb H)→ₗ[ℝ] ℝ:= {
           toFun x:= C.average Wμ (Y x)
           map_add' u v:=by rw [show Y (u+v)=Y u+Y v from ?_,sun Wμ C (hp _) (hp _)]
                            funext i; unfold Y τ2; rw [map_add,show Q ![_,_,_]=_ from (show Q ![T u+T v,p i,p i]= Q ![T u,p i,p i]+Q ![T v,p i,p i] from DFunLike.congr_fun (Q.curryLeft.map_add ..) ..)]; rw [add_div];rfl
           map_smul' c x:=by
                            rw [show Y (c • x)=c • Y x from ?_,scooted]; rfl
                            funext i; unfold Y τ2; rw [map_smul,show Q ![_,_,_]= _ from (show Q ![c • T x,p i,p i]=c*Q ![T x,p i,p i] from DFunLike.congr_fun (Q.curryLeft.map_smul ..) .. ), mul_div_assoc];rfl }
      have hh(v:G.El)(x): M (glint _ v x)=M x:=by
           let u:=glint Qµ v; change C.average Wμ (Y (glint _ v x))=C.average Wμ (Y x); rw [meanFit Wμ Wμ C C u.toLinearMap (dual_wick _ _ _ fun x=>(kin_c S he H U t h hc v x x).symm) _ (hp _)]; refine congr_arg (C.average Wμ) ?_; funext i; change Q ![T (glint _ v x),p (u i),p (u i)]/2= _; let P:= T x; let Z:= Busk S he v
           have hv: T (glint _ v x)=Z P:= (show fieldT _ _= _ from (BuskC H v x ▸ BuskT S he H U t h v x).symm); have hb:p (u i)=Z (p i):=(Buske S he H v i).symm; rw [hv,hb,show ![Z P,Z (p i),Z (p i)]=Z ∘![P,p i,p i] from funext fun i=>by fin_cases i<;> rfl]; exact congr_arg (fun x:ℝ=> (4:ℝ)⁻¹*x/2) (stillZ S he U t h ..)
      exact YM.Stationary.slot_fixed hs (M.toContinuousLinearMap) hh x
-- thermal centering s as in τ1
lemma τSolve (x: Keys G (Limb H)):
   let p:=fieldT (cabin g) (cloak H x)
   let Ux:= fieldU (cabin g) (cloak H x) (cloak H x)
   let s:= FetchS S he H G (Ux.2)
   InV S he H G s=Ux ∧ τ1 (πV S he t A 3) p (InV S he H G)= (-2:ℝ)⁻¹ • C.P s:=by
       intro p Ux s; let z:= EchoV S he H G; have hx:z s= Ux.2:= echoFetch S he H Ux.2 (fun k=>congr_arg Prod.snd (knowU S he H U h t k x x)); have hp:=viewer t h.2.1; let Y:= Ux.2; have hh:Ux=((0:Bid.Dir G c), z s):=hp.lower (cloak H x) (cloak H x) |>.trans (congr_arg (Prod.mk 0) hx.symm)
       refine ⟨hh.symm,LinearMap.ext fun aV=>?_⟩; let T:= iteratedFDeriv ℝ 2 (pane X! t A.clip A.live) 0; let Q:= iteratedFDeriv ℝ 3 (pane X! t A.clip A.live) 0; change (2:ℝ)⁻¹ * ((4:ℝ)⁻¹ * Q ![(0,z aV),p,p]) =(-2:ℝ)⁻¹ *(C.P s aV); rw [hc,← tollY S he U h t, show Q ![_,p,p]= _ from hp.reserve (z aV) (cloak H x) (cloak H x) ]; change _ *(_ * (- T ![Ux,(0,z aV)]))=(-2:ℝ)⁻¹ * (T ![(0,z s),(0,z aV)]/4);rw [hh];ring
end YM.OPE.Cascade.Rill
