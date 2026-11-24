import YM.OPE.Compatible.Cant.Fat
import YM.OPE.Compatible.Cant.Ki
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Tips.Thel
import YM.OPE.Compatible.Cant.Hoe
/-!
# The lifted bilinear form and its one-step map

`YM.OPE.Stroke.Lais` pulls the bilinear form back along `Plato` in both arguments, and `laEQ` expresses its value through `Por`.
`pulseU` computes the endomorphism `σPulse` by lifting a vector, applying one step of `Soul`, and reading the result back.
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
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "μ"=> lapPrice (Patch.L P)
-- Pull the bilinear form back along the same lift in both arguments.
noncomputable abbrev Lais (e:Fin (l+1))(t:ℕ)(V:Even n.val)(i:Phase)(x y:Site n) (A':Submodule ℝ (Bead G l e.val)): Jewel A' →ₗ[ℝ] Jewel A'→ₗ[ℝ] ℝ:= by
     let T:=Plato Z e.val A' e.isLt; let B:= (UnitBorn Hp Z a V x y i t (e:=e.val)); exact LinearMap.compl₂ (B.comp T) T
set_option maxHeartbeats 200000 in
lemma laEQ (e:Fin (l+1))(t:ℕ)(V:Even n.val)(i:Phase)(x y:Site n) (A':Submodule ℝ (Bead G l e.val))(u v:Jewel A') :
      Lais Hp Z a e t V i x y A' u v=Por Hp Z e.val i V x y a t (Plato Z e.val A' e.isLt u) (Plato Z e.val A' e.isLt v):=(flareP Hp Z a ..).symm
-- Compose the lift, the one-step operator, and the readout map.
noncomputable abbrev σPulse (e:Fin (l+1)) (A':Submodule ℝ (Bead G l e.val))(Y:Mint Z e.val→ₗ[ℝ] Jewel A'): Jewel A' →ₗ[ℝ] Jewel A':= Y.comp ((portC Z.station (lapPrice P.L e.val) 3).toLinearMap.comp (Plato Z e.val A' e.isLt))
set_option maxHeartbeats 200000 in
lemma pulseU (e:Fin (l+1)) (A':Submodule ℝ (Bead G l e.val))(Y:Mint Z e.val→ₗ[ℝ] Jewel A')(x:Jewel A'):σPulse Z e A' Y x= Y (Soul (P:=P) Z.station 1 (Plato Z e.val A' e.isLt x)):=by
        exact congr_arg Y (imagery Z.station 3 (lapPrice P.L e.val) (Plato Z e.val A' e.isLt x)).symm
end YM.OPE.Stroke
