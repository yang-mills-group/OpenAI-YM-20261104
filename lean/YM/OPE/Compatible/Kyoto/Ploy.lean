import YM.OPE.Compatible.Kyoto.Ere
import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Cloud
import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Opal
import YM.OPE.Compatible.Kyoto.TreeQ
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Cost estimates for a family of matched hosts

Assume the family satisfies `Chase` and its fine fees have upper
rate zero. For each degree, `purse1` supplies a cost of upper
rate zero. Eventually it is nonnegative and both the `Paid` estimate
and the chart licence hold. `purse2`
supplies the constants and a cost of upper rate zero for the `Rich`
estimate on the same hosts.
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
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
namespace MatchZ

section
open Lass.Zest Lass PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel
variable {Ξ:Medal P' G K.K P'.J} {P₀:Teller G}
variable {E:ConnectedActivityE6.Target G P₀} {Q:Side}{W C κ:ℝ}{o:ConnectedActivityE6.Target.Order G W}
variable (F:I→Mug P' p p' T j R Ξ)
variable (L₁:∀ i,Wall P' E Q o κ C k (F i).hostS){l₀:Filter I} (hq:Chase (Eve L₁) l₀)
local notation "ζ"=>Eve L₁
local notation "X*!"=> fate (Eve L₁)
variable {β υ ε:I→ℝ}
set_option quotPrecheck false
variable (R1:ℝ)(hV:∀ i,|MatchZ.fare ((F i).row)|≤R1)(hv:Mag P'.J j) (hp:Wage (Eve L₁) l₀ (fun i=> (F i).row.fine.fees) 0)
include H hs hq hp
lemma purse1 (d:ℕ): ∃ A:I→ℝ, Wage ζ l₀ A 0 ∧∀ᶠ i in l₀, let X:=(F i).hostS; Cascade.Paver.Paid X.Z.patch X.Z.kernel X.U X.A R 49 5 d (A i) X.b ∧ licensed X.Z X.H X.U X.A.clip X.A.live X.M X.A.sky X.g ∧ 0 ≤A i:=by
       obtain ⟨f,H,hz,hp'⟩:= fullpay H hs (fun i:I=> (F i).row.fine.ℳ) Ξ 0 49 d 5 (by omega) (fun i=>(F i).row.fine.positive) (fun i=> (F i).row.fine.clip); exact ⟨f,height_W l₀ (X*!) f id H hq.tense hp,Eventually.of_forall (fun i=>⟨hp' i,(F i).θ.permit,hz i⟩)⟩
open Limn
omit H hs in
lemma purse2 :∃ (s c' e u s':ℝ)(V:I→ℝ), (∀ᶠ i in l₀,let L:=(F i).hostS; L.b=0 ∧ L.Rich s c' e (V i) u s'∧ 0≤ V i) ∧0<s ∧0<e ∧ 0 ≤ c' ∧ Wage ζ l₀ V 0 ∧ 0 < u:=by
       obtain ⟨t,C,hW⟩:= Limn.purchased G Ξ.root (Pox T P') (cait T P' p); let V(i):= (F i).row.heftC; have hx: Wage ζ l₀ V 0:=((RateLE.const (leafC G (T.peak P'.J) 5) hq.tense).mul hp).mono (by simp)
       refine ⟨kTime T P',zCap T P' p,tupY K P',t,C,V,Eventually.of_forall (fun i=>⟨rfl,?_,heft_pos _⟩),Pox .., (SecQ K P').pos,cait ..,hx,hW.warmth⟩
       exact RoundQ (F i).row Ξ (F i).pW (F i).work hW (F i).musk 
end
end MatchZ
end
end YM.OPE.Stroke
