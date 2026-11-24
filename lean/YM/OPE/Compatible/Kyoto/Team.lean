import YM.OPE.Compatible.Kyoto.Clock
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Fine and coarse data for one lattice step

A `MatchZ` pairs a fine and a coarse stage with a fare satisfying
`Votive.Charm`. For periods related by the patch side and a step
satisfying `Bid.Larger`, `Auth` supplies a licensed chart. Given the
fibre representation, `Touch` verifies the licence for the resulting host.
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
structure MatchZ (B:Patch)(p p':Clip)(T:Seasons K)(j:ℕ) (R:ChartRatio G) where
        fine: Cab T B.J p
        coarse : Cab T j p'
        fare : ℝ
        bound : Votive.Charm B.L fine.ℳ coarse.ℳ fare R
namespace MatchZ
variable (D:MatchZ P' p p' T j R)
local notation "F'"=>MatchZ P' p p' T j R
local notation "S'"=>D.fine.ℳ
abbrev journey := iotaK P' D.bound.mag D.fine.ℳ.gear
variable (B:Medal P' G K.K P'.J) {hx:f.val=c.val*P'.L.val}
abbrev SlotF (h:f.val=c.val*P'.L.val) :StepData c f:= StepData.mk P' K.K h
set_option quotPrecheck false
local notation "W"=>SlotF (P':=P') (K:=K) hx
lemma allowsG :(D.journey.visit K.K hx)= (W):=by cases P'; rfl 
lemma finalP : D.coarse.ℳ.gear=D.journey.land:=endV _ _ D.bound.mag D.bound
abbrev Roma := charmSeal B (S').gear
local notation "O"=>D.Roma B
noncomputable abbrev SeatM (h:f.val=c.val*P'.L.val):=installed (SlotF (P':=P') (K:=K) h|>.ratio) (D.journey.duo K.K.penalty).A0
structure Can (h:f.val=c.val*P'.L.val) where
        (z: Bid.Dir G c→ AxisChart G (forest (SlotF (P':=P') (K:=K) h).ratio P'.odd_side))
        permit : licensed (SlotF (P':=P') (K:=K) h) P'.odd_side (D.Roma B) D.fine.ℳ.clip D.fine.ℳ.live (D.SeatM h) D.fine.ℳ.sky z
lemma Auth (h: Bid.Larger (G:=G) (W)): Nonempty (Can D B hx):=by
        -- The visit uses the patch ratio by definition, and finalP identifies its landing gear.
        obtain ⟨g,hg,-⟩:= testimony D.journey K T S' D.coarse.ℳ rfl D.finalP D.bound.mag B (ha:=hx) (hs:=h); exact ⟨g,hg⟩
variable (N:Rep G f)(s:(SlotF (K:=K) (P':=P') hx).Choices)
noncomputable abbrev Plotter (M:Can D B hx)(s:(SlotF (K:=K) (P':=P') hx).Choices):=FibreRep (W) P'.odd_side (O) s S' M.z 0
variable (C₁ :Can D B hx)
set_option maxHeartbeats 200000
include hs in lemma Porter : Nonempty (FibreRep W P'.odd_side O s S' C₁.z 0):= enrol W P'.odd_side O s C₁.permit _ hs 
variable (F :FibreRep (SlotF (P':=P') (K:=K) hx) P'.odd_side (D.Roma B) s D.fine.ℳ C₁.z 0)
noncomputable abbrev booth (N:Rep G f): Host K T:= ⟨c,f,W,P'.odd_side,P'.J,D.fine.fees,S',O,0,N,D.SeatM hx,C₁.z,s,F⟩
local notation "Uμ"=>D.booth (hx:=hx) (c:=c) (f:=f) B s C₁ F N
open Silt.Phere
lemma Touch : Licence (Vpass Uμ) (united (Vessel K.K D.coarse.ℳ.gear G c D.bound.mag.2.1) (Uμ).F.L.Q) (S').gear K.K:=by
       rw[D.finalP]; exact Vauth D.journey S' B D.bound.mag rfl c f hx 0 N s _ C₁.permit F
end MatchZ
end
end YM.OPE.Stroke
