import YM.OPE.Compatible.Rave.Orb
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Hike.Piece
import YM.OPE.Compatible.Karls.Bent
import YM.OPE.Compatible.Karls.York
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
open Finset
open PriceZ Hark
-- abstract station weighted block
open Hark
section general
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {u r q:ℝ}
variable {g:E≃ₗ[ℝ] (Fin 3→ F)}{B:Phase→Dice E}{S T:E→L[ℝ] E}
variable (X:Thruster g S T q)(Z:Ding B S)
local notation "SX" i:arg a:arg => g.symm (Pi.single (M:=fun _ : Fin 3=>F) i a)
include X
include Z
lemma vanSpice (p q':E)(hp:g p 0=0):Spice q T B p q'=0 ∧ Spice q T B q' p=0:=by obtain ⟨h,hv⟩:= Z.upper X (Ux T q p) q' (X.ebb _) (X.rise p hp); unfold Spice; rw [h,hv,Z.lows X p (Ux T q q') hp (X.ebb _), Z.lows X (Ux T q q') p (X.ebb _) hp, add_zero]; exact ⟨rfl,rfl⟩ -- maybe goals
lemma spice_equal (x x' y y':E)(h:g x 0=g x' 0)(hx:g y 0=g y' 0): Spice q T B x y=Spice q T B x' y':=by
    have he:= (vanSpice X Z (x-x') y (by rw [map_sub,Pi.sub_apply,h,sub_self])).1; have hh:=(vanSpice X Z (y-y') x' (by rw [map_sub,Pi.sub_apply,hx,sub_self])).2; unfold Spice at he hh ⊢; simp only[map_sub,_root_.sub_apply] at he hh; linarith
end general
end YM.OPE.Quit.Jac
