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
# The same matched step in fine and coarse coordinates

A `Mug` records the two lattice periods, their representations, and
the licensed fibre data for a matched row. At the stated stage bounds,
`Alc` identifies the action of `Flail` shifted by the negative fare
with the transport induced by `Stint`. Along a diverging clock with fine fees of upper
rate zero, `Flail_pay` shows that this action preserves `Alive`.
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

structure Mug (P':Patch)(p p':Clip)(T:Seasons K)(j:ℕ)(R:ChartRatio G)(B:Medal P' G K.K P'.J) where
       row : MatchZ P' p p' T j R
       (c f:Side)
       eraX : f.val=c.val*P'.L.val
       pW:Rep G f
       pV: Rep G c
       musk : Zeph.fitsW row.fine.ℳ pW
       θ : Can row B eraX
       ruby : (SlotF (P':=P') (K:=K) eraX).Choices
       work : FibreRep (SlotF (P':=P') (K:=K) eraX) P'.odd_side (row.Roma B) ruby row.fine.ℳ θ.z 0

variable {B:Medal P' G K.K P'.J}
local notation "𝓜"=>Mug P' p p' T j R B
set_option quotPrecheck false
noncomputable abbrev Mug.hostS (X:Mug P' p p' T j R B):= X.row.booth (hx:=X.eraX) (c:=X.c) (f:=X.f) B X.ruby X.θ X.work X.pW
variable (U:Mug P' p p' T j R B)

variable (V:Foyer L hs a l d)
private lemma cancelCoordinates {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (source target : A ≃L[ℝ] B)
    (action : B →L[ℝ] B) (x : B) :
    action x = target (target.symm (action (source (source.symm x)))) := by
  rw [source.apply_symm_apply, target.apply_symm_apply]

include H hs
lemma mugTar : RollD U.hostS.A U.hostS.U R:= ⟨hs,H,(sportB U.row B H).eph⟩ 
include V
noncomputable def Flail (x:solar G d V.pay.st.τ): solar G d V.pay.st.τ:= Rito (vν:=fun i:𝓜=> i.row.fine.fees) H hs (fun i=>i.row.fine.ℳ) B U (fun i=> (sportB (i.row) B H).eph) V.pay.st.hτ x
private abbrev fineCoordinates := Fallix G V.pay.st.hτ K U.row.fine.ℳ.gear P'.order_cut
private abbrev coarseCoordinates := Fallix G V.pay.st.hτ K U.row.coarse.ℳ.gear U.row.bound.mag.2.1
private abbrev enacted := yankV U.row.coarse.ℳ (sportB U.row B H) H hs V.pay.st.hτ

private lemma enrolledAction (x : solar G d V.pay.st.τ) :
    Ibis.vintage G V.pay.st.hτ (-U.row.fare) (Flail U V x) = enacted U V x := rfl

private lemma shiftedCoordinate (z : Tracts G d V.pay.st.τ) :
    Stint V U.row B z =
      (coarseCoordinates U V).symm (enacted U V (fineCoordinates U V z)) := rfl

private lemma transportedAction (x : solar G d V.pay.st.τ)
    (he : highStage L hs a V ≤ P'.J) (ht : highStage L hs a V ≤ j)
    (move : Tracts G d V.pay.st.τ →L[ℝ] Tracts G d V.pay.st.τ) :
    Emote (D₀ := V.pay.st.stars) (hp' := V.pay.st.S.order_cut.trans ht)
      (hp := V.pay.st.S.order_cut.trans he) (V := Cab.ℳ) (DΦ := Cab.ℳ)
      U.row.fine U.row.coarse move x =
    coarseCoordinates U V (move ((fineCoordinates U V).symm x)) := rfl

private lemma reenrolled (x : solar G d V.pay.st.τ) :
    enacted U V x = coarseCoordinates U V (Stint V U.row B ((fineCoordinates U V).symm x)) :=
  (cancelCoordinates (fineCoordinates U V) (coarseCoordinates U V) (enacted U V) x).trans
    (congrArg (coarseCoordinates U V)
      (shiftedCoordinate U V ((fineCoordinates U V).symm x)).symm)

set_option maxHeartbeats 200000 in
lemma Alc (x:solar G d V.pay.st.τ)(he:highStage L hs a V ≤ P'.J)(ht:highStage L hs a V ≤ j) : Ibis.vintage G V.pay.st.hτ (-U.row.fare) (Flail U V x)= Emote (D₀:=V.pay.st.stars) (hp':=(V.pay.st.S.order_cut.trans ht)) (hp:=(V.pay.st.S.order_cut.trans he)) (V:=Cab.ℳ) (DΦ:=Cab.ℳ) U.row.fine U.row.coarse (Stint V U.row B) x:=by
  exact (enrolledAction U V x).trans ((reenrolled U V x).trans
    (transportedAction U V x he ht (Stint V U.row B)).symm)
variable (F:I→Mug P' p p' T j R B) {f:Filter I}{c:I→ℝ} {x:I→solar G d V.pay.st.τ}
open Ibis
lemma Flail_pay (hv:Tendsto c f atTop)(hp:RateLE f c (fun i=> (F i).row.fine.fees) 0)(hx:Alive f c x): Alive f c (fun i=>Flail (F i) V (x i)):=by
        exact GrowthU H hs (fun i:𝓜 =>i.row.fine.ℳ) B (fun i=> (sportB i.row B H).eph) V.pay.st.hτ F (fun i=>i.row.fine.positive) (fun i=>i.row.fine.clip) hv hp hx
end MatchZ
end
end YM.OPE.Stroke
