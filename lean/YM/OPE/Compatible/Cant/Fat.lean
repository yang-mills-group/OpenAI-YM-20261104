import YM.OPE.Compatible.Cant.Orb
import YM.OPE.Compatible.Cant.Hoe
/-!
# Bilinear pairings of lifted readouts

`YM.OPE.Stroke.ParD` uses the `Bals` decomposition to replace both inputs of `Por` by their lifts through `Plato` without changing the pairing.
At pinned sites on an even lattice satisfying the barrier bound, the two residuals lie in `Dross` and vanish in their respective arguments.
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
open Pipes
noncomputable abbrev PledgeD (t:ℕ)(w:Even n.val)(x y:Site n)(i:Phase)(r:ℕ): Mint Z t →ₗ[ℝ] Mint Z t→ₗ[ℝ] ℝ:=UnitBorn Hp Z a w x y i r
lemma ΔEQ' [hj:AddCommGroup E][Module ℝ E](f:E→ₗ[ℝ] E→ₗ[ℝ] ℝ)(p q x y:E)(h:f (p-q) x=0)(hx:f q (x-y)=0) : f p x=f q y:=by
       have he': f q x=f q y:=sub_eq_zero.mp (by rw [← map_sub]; exact hx); rw [← he']; exact sub_eq_zero.mp ((show f p x-f q x=0 from (by rw [map_sub,LinearMap.sub_apply] at h; exact h)))
set_option maxHeartbeats 200000 in
lemma ParD {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(e:J!)(V:Even n.val)(x y:Site n)(hz:barrier P≤ n.val)(ht:Pins K P x y)(p q:Mint Z e.val)(r:ℕ)(i:Phase):Por Hp Z e.val i V x y a r p q= Por Hp Z e.val i V x y a r (Plato Z e.val (A' e.val) e.isLt (κ e p)) (Plato Z e.val (A' e.val) e.isLt (κ e q)):=by
      let Q:= Plato Z e.val (A' e.val) e.isLt; let U:= Q (κ e p); have hp:p-U∈Dross Hp Z a e.val:= C.tricks e|>.slice p; let v:=Q (κ e q); have hv:q-v∈Dross Hp Z a e.val:= C.tricks e|>.slice q; simp_rw[flareP]; exact ΔEQ' (E:=↥(Fruition Z.station (lapPrice P.L e.val))) _ p U q v (hp _ _ x y hz ht r i q|>.1) (hv _ _ x y hz ht r i U|>.2)
end YM.OPE.Stroke
