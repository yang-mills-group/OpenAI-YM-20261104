import YM.OPE.Compatible.Jess.Rim
/-! # Thermal pedal comparing arbitrary period -/
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
variable (S:StepData c f)(he:Odd S.ratio.count.val)(B:Boxes G S.patch S.kernel)(A:Alps K T i v)(P:ChartRatio G) {W: Matrix (Body 1 f) (Body 1 c) ℝ}
local notation "X!"=>forest S.ratio he
local notation "K!"=> Bid.Dir G c
local notation "D!"=> AxisChart G (forest S.ratio he)
variable (g:Bid.Dir G c→AxisChart G (forest S.ratio he))(t:S.Choices) (hk: licensed S he B A.clip A.live W A.sky g)(ht: LocalRatio P)(hs:G.Simple)
variable (X:FibreRep S he B t A g u)(Y:FibreRep S he B t (i:=i) A g b)
lemma orth :X.L.Q=Y.L.Q:=by
     have hu (L R:Law (AxisChart G (forest S.ratio he)))(h:L.P=R.P):L=R:=by cases L; cases R; simp_all
     exact hu _ _ (LinearMap.ext fun x=> LinearMap.ext fun y=> (X.P0 x y).trans (Y.P0 x y).symm)
include hk
lemma originJ (x:K!×D!) : jet X.L.f 2 x= jet (pane X! t A.clip A.live) 2 x:=by
     unfold jet; let y:=pane X! t A.clip A.live; have hh:X.L.f=ᶠ[𝓝 0] (y-fun _=>y 0):=X.meter; rw [(hh.iteratedFDeriv ℝ _).eq_of_nhds,iteratedFDeriv_sub_apply (show ContDiffAt ℝ _ y 0 from (viewer t hk.2.1).origin.of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (by decide),Pi.zero_apply,sub_zero]
include ht hs
lemma crank (x:K!)(y:D!): Flash A P S he t B g x Y y= Flash A P S he t B g x X y + merry ((-(b-u))*X.L.u_q x-(b-u)*X.L.Q.P y y/2):=by
     let F:=pane X! t A.clip A.live; let U:= (Fiber.drape K! D! X.L.M) (x,y); let Hp:= (viewer t hk.2.1).origin
     change Adhesion.Curling Y.L.f _ _= Adhesion.Curling X.L.f (X.L.wSign P) U+_; rw [show Y.L.M=X.L.M from Y.M.trans X.M.symm]; erw [gumbar S he B t hk ht X U hs,gumbar S he B t hk ht Y U hs, show jet (HaloC S he t b A P) 2 U= _ from (Rill.bandC S he t ht b Hp U).2, show jet (HaloC S he t u A P) 2 U= _ from (Rill.bandC S he t ht u Hp U).2]; have hv: jet F 2 U=X.L.u_q x+ X.L.Q.P y y/2:=by rw [← originJ S he B A g t hk X]; exact X.L.split ..
     rw [show jet (pane X! t A.clip A.live) 2 U= _ from hv]; unfold merry flareTok; apply JetS.eta <;> simp; ring
-- dress Q
lemma star_base (R:T!)(h:Aware d τ)(z:Site c)(x:K!):
     let v:=TracePay S he B A t g P d (spread G d τ R) u z X
     let w:=TracePay S he B A t g P d (spread G d τ (rebase G h (b-u) R)) b z Y
     w x=v x+ merry (((b-u)/2)*deriv (fun i:ℝ=>(v (i • x)).s) 1):=by
      intro v' w'; let U: K! × D!→L[ℝ] Bid.Dir G f:= ribz S he ∘L (Fiber.drape K! D! X.L.M).toContinuousLinearMap; let p: ScriptJ (Bid.Dir G f):=inkM (spread G d τ R) d (S.ratio.embed z); let f:= p ∘ U
      let A':= Chart.tangent G (forest S.ratio he).Free; have hp:ScriptJ.B f := fun i=> ((meridian _ _ 0 _ _ (resin R (fun i=>Nat.zero_le _))) i).compLinear U.toLinearMap -- pathic not needed
      let q(u):=Flash A P S he t B g u X; let a:= Flash A P S he t B g x Y; let c':= b-u; have hx(y:D!) : bitH A S he t B g z x Y (spread G d τ (rebase G h (b-u) R)) d y = f (x,y)+ merry ((c'/2)*deriv (fun t:ℝ=> (f (t • (x,y))).s) 1):=by
           unfold bitH; rw [show Y.L.M=X.L.M from Y.M.trans X.M.symm,flot]; simp only [f,Function.comp_apply]; rw [funext (show ∀ t:ℝ,_ from fun t=> congr_arg (fun x=> (p x).s) (U.map_smul t (x,y)))]; rfl
      unfold v' w'; simp_rw [timely]; rw [funext hx,← orth S he B A g t X Y]; apply topD A' X.L.Q _ f q a hp x ((-(b-u))*X.L.u_q x) (flared A P S he t B g x X ht) (fun i y=> Adhesion.curT (X.L.signPay ht) _) (fun i=> crank S he B A P g t hk ht hs X Y x i)
end YM.OPE.Drift
