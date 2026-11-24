import YM.OPE.Compatible.Cres.Sake
/-!
# Rate bounds for the quadratic reading `τPledge`

`ζPlan` gives an exponent-zero bound for the reading when the field and frame
have exponent zero and the parameter has exponent `u ≤ 0`. `ζLeap` compares two
parameters by factoring the difference of their squares. The difference of the
readings then has the same rate bound as the difference of the parameters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
open Silt.Phere

section bookkeeping
open Ibis
local notation "p!"=> LineCt W
local notation "v!"=> solar G d τ
lemma shake0 (A:Phase)(v : p!): Energy A W v= PlaS E! A v:=rfl
lemma ζshot (t:ℝ)(x:v!): τPledge D j' t x=FilmP E! t (Eout D j' x):=rfl
variable (f:I→M) {L:Filter I}{T W' α γ δ:I→ℝ}
lemma rakeQ [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {X:I→ E→L[ℝ] F}{f:I→E}{v b:ℝ}(hf:RateLE L T f b)(h:RateLE L T X v): RateLE L T (fun i=> X i (f i)) (v+b):=RateLE.bil h hf (Eventually.of_forall fun i=>(X i).le_opNorm (f i)) 
variable (hL:Tendsto T L atTop) (hF:RateLE L T (Y∘ f) 0)
variable (P0:I→solar G d τ)(hP:RateLE L T P0 0)
include hL hF hP
lemma ΓForm : RateLE L T (fun i=> Eout D (f i) (P0 i)) 0:=by
       let F:=(FallWeather (K:=K) D₀.aware (fun i=>(V i).gear) hp Y hq).2; apply (rakeQ (X:=fun i=> Eout D (f i)) hP (v:=0) ?_).mono (by simp); exact (height_W _ _ (fun i=>Eout D i) _ (PledgeW (pricedA' Hp Z a W U hq hp V D) F) hL hF) 
-- Compare the same reading at two parameter values.
variable (hZ:RateLE L T W' u)(hu':u ≤ 0)(hx:RateLE L T δ 0)(hq':RateLE L T (fun i=> δ i-W' i) v)
include hZ hu'
lemma ζPlan : RateLE L T (fun i=> τPledge D (f i) (W' i) (P0 i)) 0:=by
        have he(j:Phase): RateLE L T (fun i=>Eψ D (f i) j (P0 i)) 0:=(rakeQ hP (height_W L T _ _ (Ecost D j) hL hF)).mono (by simp); let h:= hZ.mono hu'; exact (((he 0).add ((h.smul (he 1)).mono (by simp)) hL).add (((h.pow 2 hL).smul (he 2)).mono (by simp)) hL) 
include hx hq'
lemma ζLeap : RateLE L T (fun i=> τPledge D (f i) (δ i) (P0 i)-τPledge D (f i) (W' i) (P0 i)) v:=by
       let g(i:I)(j:Phase):= Eψ D (f i) j (P0 i); have he(j): RateLE L T (fun i=>g i j) 0:=(rakeQ hP (height_W L T _ _ (Ecost D j) hL hF)).mono (by simp); apply ((hq'.smul (he 1)).mono (by simp) |>.add (((hq'.mul (hx.add (hZ.mono hu') hL)).smul (he 2)).mono (by simp)) hL).congr
       filter_upwards with i; change (δ i-W' i) • g i 1+ ((δ i-W' i)*(δ i+W' i)) • g i 2=g i 0+δ i • g i 1+(δ i)^2 • g i 2-(g i 0+W' i • g i 1+(W' i)^2 • g i 2); module
omit hx hq'
end bookkeeping
end
end YM.OPE.Stroke
