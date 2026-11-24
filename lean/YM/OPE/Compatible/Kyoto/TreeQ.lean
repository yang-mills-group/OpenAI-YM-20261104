import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Local bounds for the host of a matched step

`RoundQ` constructs the host's `Rich` bounds from the `VaultC`
estimate and the condition `Zeph.fitsW` on the fine representation.
The constants come from the patch certificate and the stage bounds.
The nonnegative cost `heftC` scales with the fine fee.
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
variable (V:Foyer L hs a l d) {hk:highStage L hs a V≤ P'.J}{he:highStage L hs a V ≤ j}
variable (X:BankW L hs a V hk p)
namespace MatchZ
open Work.F03 YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model Limn
variable (D:MatchZ P' p p' T j R)(B:Medal P' G K.K P'.J)
set_option quotPrecheck false
variable {hx:f.val=c.val*P'.L.val}(N:Rep G f) {k': (SlotF (P':=P') (K:=K) hx).Choices}{C₁:Can D B hx}
variable (F:FibreRep (SlotF (P':=P') (K:=K) hx) P'.odd_side (D.Roma B) k' D.fine.ℳ C₁.z 0)
local notation "Y"=> D.booth (hx:=hx) (c:=c) (f:=f) B k' C₁ F N
noncomputable def certificate (G:Gauge)(P:Patch)(K:KernelChoices)(H:P.Branches K G): Sheds G P K:= sets _ (Classical.arbitrary _) H
noncomputable abbrev SecQ (K:Sponsor G)(P:Patch):= certificate _ _ _ (K.affordable P)
noncomputable abbrev kTime (T:Seasons K)(P:Patch):=Estimate.down (T.peak P.J) 5
noncomputable abbrev zCap (T:Seasons K)(P:Patch)(x:Clip):=crownC (SecQ K P) (T.peak P.J) (T.gradeL P.J) x 5
noncomputable abbrev tupY (K:Sponsor G)(P:Patch):= SecQ K P|>.b
lemma Pox (T:Seasons K) (P':Patch) : 0 < kTime T P':=down_pos 5 (T.positive _)
lemma cait (T:Seasons K)(P':Patch)(p:Clip) :0≤ zCap T P' p:=le_max_left ..
lemma sureQ :0<tupY K P':= (SecQ K P').pos
noncomputable abbrev heftC := leafC G (T.peak P'.J) 5*D.fine.fees
variable {s b':ℝ}(ht:VaultC G (kTime T P') (zCap T P' p) B.gap s b')
set_option synthInstance.maxHeartbeats 260000
set_option maxHeartbeats 200000
include ht
lemma RoundQ (hV:Zeph.fitsW D.fine.ℳ N): (Y).Rich (kTime T P') (zCap T P' p) (tupY K P') D.heftC s b':=by
        let S:=SlotF (P':=P') (K:=K) hx; let H:= (SecQ K P'); let D':= D.fine.ℳ; let T':=forest S.ratio P'.odd_side; have hc:= crownPay (m:=5) S T' k' (K.affordable P') H D'.pays; have hq:= leafPay (m:=5) S T' H D'.pays; refine ⟨hV,C₁.permit,ht,⟨BoneC S T' H D'.live D'.clip,?_⟩,BoneL S T' D'.live,hq.pays,hq.meter,fun i x hx j hj=>hq.voice i x hx j ((le_trans hj (by decide : 3≤5)))⟩ 
        let p0:= BoneC S T' H D'.live D'.clip; unfold zCap; exact (congr_arg (fun y=> Dew.Pile S T' H.b (crownC H (T.peak P'.J) (T.gradeL P'.J) y 5) (Estimate.down (T.peak P'.J) 5) 5 (pane T' k' D'.clip D'.live) p0) D.fine.clip).mp hc
omit ht in lemma heft_pos :0 ≤ D.heftC:= mul_nonneg (le_max_left ..) (zero_le_one.trans D.fine.positive)
end MatchZ
end
end YM.OPE.Stroke
