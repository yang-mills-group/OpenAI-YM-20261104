import YM.OPE.Compatible.Swoon.Grid
/-!
# Color trace of yy-charge exact vanish. Based on full-F Hess positive, all centers bought
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
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- define τ21 etc log residual. use coherence E conditional. uniform proof later
abbrev DriftH (g:Bid.Dir G c→AxisChart G X!)(A: Alps K T i v)(D: Alps K T d u)(P:ChartRatio G)(r b:ℝ)(C:Law J!)(x: Bid.Dir G c):ℝ:=
     let w:= fieldT (cabin g) x
     let z:=fieldU (cabin g) x x
     let t₃:=πV S he t A 3
     let t₄:=πV S he t A 4
     let y:= InV S he H G
     jet (HaloC S he t r A P) 2 w-jet (haloP b D) 2 x-C.average Wμ (τ21 t₄ w y)+ (C.average Wμ ((τ2 t₃ w y)^2))/2 - C.average Wμ (τ2 t₃ z y)/2
-- main
include S he H X U ht g t K G h C hc
lemma inclusive (hS:G.Simple)(α:ℝ)(hh:TEX U A.clip D.clip A.live D.live α P)(x:P!):
    draw (fun y:J!=> (Y.L W!).hat P (Tight S he H X g (x,y))) C Wμ=
    draw (fun y:J!=> (Y.L W!).hat P (Tight S he H X g (0,y))) C Wμ * ((V.L X).hat P x * flareTok 0 (DriftH S he H t g A D P r b C (rayS H X G x))) :=by -- b relation needs V b yes drift arbitrary
       let τ:=πV S he t A 3; let Q:=πV S he t A 4; let p:= rayS H X G x; let w:= fieldT (cabin g) p; let y:=InV S he H G; let v:= fieldU (cabin g) p p; let z:= FetchS S he H G v.2; have hF:= viewer t h.2.1
       let Yh:=HaloC S he t r A P; have hp:ContDiffAt ℝ ω Yh 0:= (bandC S he t ht r hF.origin w).1
       have hu:Tensor.Sym τ:= polarπ S he U t h 3; have hz:Tensor.Sym Q:= polarπ S he U t h 4
       have hb:C.average Wμ (τ2 τ w y)=0:=τFlat S he H U t h hc hS (X.rollX x); obtain ⟨hv,hd⟩:= τSolve S he H U t h hc (X.rollX x); have hr:jet (looper P) 2 (0:P!)=0:=by rw [njet, ContinuousMultilinearMap.map_coord_zero _ (0:Fin 2) (by rfl),_root_.zero_div]
       rw [crest S he H X U t h Y ht x, crest S he H X U t h Y ht 0, map_zero, show fieldT (cabin g) 0=0 from map_zero (fderiv ℝ (viewS (cabin g)) 0),hr,nul Wμ C τ Q Yh y hu hz hp, SwiftD H X V ht hS x]
       dsimp only; let M:= swornV D.clip D.live (n:=c); have hh' := rankparse S he H U t h hc α P hh (X.rollX x);
       change jet M 3 p/4=τ0 τ w∧ jet M 4 p/4=τ4 Q w-C.P z z/8 at hh'; simp only [neg_div]; rw [show jet M 3 p/4=_ from hh'.1,show jet M 4 p/4=_ from hh'.2, blazeTok,add_zero, coheres Wμ C τ Q Yh y hu hz hp w _ z hb hd,show y z=v from hv]; apply congr_arg; apply congr_arg; unfold DriftH; change -τ4 Q w+jet Yh 2 w+jet _ 2 x -_+_+_-_= -(τ4 Q w- _)+jet (haloP b D) 2 p+jet (looper P) 2 x+(jet Yh 2 w-jet (haloP b D) 2 p-C.average Wμ (τ21 Q w y)+ _ -C.average Wμ (τ2 τ v y)/2); unfold Q Yh v τ y;ring
end YM.OPE.Cascade.Rill
