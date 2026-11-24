import YM.OPE.Compatible.Tune.Price
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Normalized frames at the retained levels

`GlowPack` records the subspaces, coefficient maps, even sides, and normalized
frames at levels `0` through `l`. Under `Lance X`, `l + l < k`, and the
stated upper and lower bounds on `τ`, `contender` constructs a pack by
choosing complements to `Ghost G l i` and normalizing each retained frame.
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
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
noncomputable abbrev PicoH {G:Gauge}(d:ℕ) (W:(i:ℕ)→Submodule ℝ (Bead G d i))(t:Fin (d+1)):=Brane (↥(W t.val))
local notation "μ"=>lapPrice (Patch.L P)
private abbrev normalizedFrame (W : (i : ℕ) → Submodule ℝ (Bead G l i)) (e : J!)
    {side : Side} (even : Even side.val) (read : Mint Z e.val →ₗ[ℝ] Jewel (W e.val))
    (frame : Jewel (W e.val) ≃ₗ[ℝ] Jewel (PicoH l W e)) : Prop :=
  Auth (Lore frame (Lγ Hp Z a e (W e.val) even)) (Kw frame (σPulse Z e (W e.val) read)) (μ e.val)

set_option maxHeartbeats 200000 in
-- At each level, `normalizedFrame` uses the same frame for `Lore` and `Kw`.
structure GlowPack where
      W:(i:ℕ)→ Submodule ℝ (Bead G l i)
      pay (e: J!) : Mint Z e.val→ₗ[ℝ] Jewel (W e.val)
      trial : Bals Hp Z a W pay
      scope (i: J!) : Side
      evenK (i:J!): Even (scope i).val
      fund (i:J!): GlowK (k:=k) Hp Z a i (W i.val) (evenK i)
      fro (i:J!): Jewel (W i.val) ≃ₗ[ℝ] Jewel (PicoH l W i)
      vnd (i:J!): ↥(W i.val)≃ₗ[ℝ] (PicoH l W i)
      tal (i:J!):Honest (fro i) (vnd i)
      authL (i:J!): normalizedFrame Hp Z a W i (evenK i) (pay i) (fro i)
variable (hp:l+l< k)(hb:∀ i,τ i≤ m)(ha:∀ i,Rise.stamp' d G k+44≤ τ i)(hP:∀ i,Variance.StencilTax d k≤ τ i)(hx:l*l≤ τ 0)(L:Lance X)

include L hp hb ha hP hx
set_option maxHeartbeats 200000 in
lemma contender : Nonempty (GlowPack Hp Z a (k:=k)):=by
       choose v hv using fun i=> (Submodule.exists_isCompl (p:=Ghost G l i)); obtain ⟨f,hf⟩:= Scout Hp Z a hp hb ha hP hx v (fun i=>hv i) L; choose n hn using fun e:Fin (l+1)=> (readyV (e':=e) Hp Z a hf hb ha hp L).exists; choose Q X hQ he using fun e:Fin (l+1)=> albora (sightH Hp Z a e (wagon_h (n e)) hf (hn e)); exact ⟨v, f,hf, fun i=>wagonN (n i),fun i=>wagon_h _,hn,Q,X,hQ,he⟩
end YM.OPE.Stroke
