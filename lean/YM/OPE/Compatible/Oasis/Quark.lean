import YM.OPE.Compatible.Oasis.Pure
import YM.OPE.Compatible.Kyoto.Orbs
import YM.OPE.Compatible.Oasis.Ball
import YM.OPE.Compatible.Kyoto.Ploy
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
# Norm bounds for an invertible frame transport

`PrimC` requires the fine-to-coarse operator `engine` to come from
a complex-linear equivalence satisfying `Treaty`. Under the matched
clock and patch hypotheses, `Pierce` obtains an eventual common bound
of upper rate zero for its norm and inverse norm. `ArcZ` bounds both
by `ages u` of the coarse time for every positive exponent `u`.
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
variable {n c f:Side}{I J :Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
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
variable {Q:ℕ}
open Limn CardinalQ Labels Source Cameo Spells Yolk Pill
open Next.Scheduling
variable {X₀:Uniform G P'}
variable (N:Foyer L hs a l (d+6)){hp:highStage L hs a N≤ P'.J}{hz:highStage L hs a N ≤ j}
variable {M:Cab T j p}{β:I→ℝ}{l₀:Filter I}
variable {T1 T2:RG.Stage}(W:∀ i, Pillar X₀ (F i) (β i)) (h:Tendsto β l₀ atTop) (hc:∀ i,Aud X₀ (F i) T1 T2 (β i) (W i))
local notation "ζ"=> Eve W
local notation "Γ"=>βM ζ
variable (hZ:Mag P'.J j)(hb:P'.L=N.pay.st.S.L^m)
variable (Y₀:BankW L hs a N hp p)(C₀:BankW L hs a N hz p')

section
open Lake(Flyer Treaty)
set_option quotPrecheck false

local notation "YC"=>fun i=> (F i).row.fine
local notation "Y*"=>fun i=>(F i).row.coarse
variable {r:ℝ}
abbrev engine (U:Mug P' p p' T j R Ξ):= Adventure N Y₀ C₀ P'.L (Stint N U.row Ξ) U.row.fine U.row.coarse (Clock.gap U.pW.beta)
structure PrimC (t u:ℝ)(M:Mug P' p p' T j R Ξ):Prop where
       viable :∃ Z: BoxQ (dims N)≃L[ℂ] BoxQ (dims N), Z.toContinuousLinearMap=engine N Y₀ C₀ M ∧ Treaty (P'.L.val:ℝ) (Reven (κBit N) t (now t G P')) u (E:=fun i=>BC (dims N i)) Z
include h hc hZ hb
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
lemma Pierce : ∃ v:I→ℝ, Wax β l₀ v 0 ∧ ∀ᶠ i in l₀, PrimC N Y₀ C₀ (β i) (v i) (F i):=by
        let p0:= helm F W h hc; let V:= Hort F W h hc; have hd:∀ᶠ i in l₀, (βM (Eve W)) i - β i=Δfare G P'.L:=by filter_upwards with i; rw [horn F W hc]; unfold ForeQ now; ring
        let f(i:I):= Clock.gap (F i).pW.beta
        have ht':∀ᶠ i in l₀, βM (Eve W) i*(f i)^2 ≤2:= by
             filter_upwards [p0.port,p0.Dscale,p0.high.eventually_gt_atTop 0] with i hi he hm; have ha:= he.1; have hv: βM ζ i/2 ≤ (F i).pW.beta := hi.budget.2.2.2.2.2.1
             have hh: (F i).pW.beta=(f i)⁻¹^ (2:ℕ):=he.2; rw [hh,inv_pow] at hv; let z:= f i; have hx:0≤ z:= by exact ha.le
             have hp:(βM ζ i/2)*z^ (2:ℕ) ≤ 1:=(mul_le_mul_of_nonneg_right hv (sq_nonneg z)).trans_eq (inv_mul_cancel₀ (pow_ne_zero _ (show z≠0 from ha.ne'))); linarith only [hp]
        obtain ⟨v,hv,ht⟩:= ΡLift F _ (fun i=>(hc i).flare) hZ N Y₀ C₀ hb hd p0.tense p0.high (f_Price F W h hc) (y_Price F W h hc) ((canq p0.high).pays p0.tense) (p0.ζOpR.pays p0.tense) ht'; refine ⟨v,Ωζ p0.high h V.Currency hv,ht.mono (fun i hi=>?_)⟩ ; obtain ⟨x,hx,h⟩:=hi; exact ⟨x,hx,(by have hh := congr_fun (horn F W hc) i; rw[hh] at h; exact h)⟩
lemma ArcZ (hg:0 < u):∀ᶠ i in l₀, PrimC N Y₀ C₀ (β i) (ages u (β i)) (F i):=by
         obtain ⟨v,hv,hp⟩:= Pierce F N W h hc hZ hb Y₀ C₀; filter_upwards [hp,hv _ hg] with i hp hi; obtain ⟨x,hx,hc⟩:=hp.viable; have hz:v i ≤ ages u (β i):=(Real.le_norm_self _).trans hi; exact ⟨x,hx,hc.toC,hc.ofC,hc.grace,hc.value,hc.charge.trans hz,hc.inverse.trans hz⟩
end
end
end MatchZ
end
end YM.OPE.Stroke
