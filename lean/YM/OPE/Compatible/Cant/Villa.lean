import YM.OPE.Compatible.Cant.Snow
/-!
# First components of flag readouts under transport

`YM.OPE.Stroke.pupil` proves that matching phase-zero values of flag representatives give readout components related by the factor `(lapPrice P.L e.val)^r` under the transport.
`InVivid` describes target readouts represented modulo the target `Sapling` submodule. `tokensPlus` and `tokensGrow` prove closure under addition and the shift `WaneZ`.
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
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
variable {uα:I→ℝ}{A:(v:I)→Alps K T j (uα v)}
local notation "μ"=>lapPrice (Patch.L P)
section
variable (hX: Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
variable {ht:4 ≤ j}{hz:1≤uα}{U':Z.Ω I uα}
variable (he: Z.Floss A U' ht (le_trans zero_le_one hz) k Hp a)(f':Tracts G d τ→L[ℝ] Tracts G d τ) (i':M)(j':I)
local notation "AC"=> Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f'
local notation "CΓ"=>Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j'
private lemma matchPhaseReadouts {E F : Type*} (tap : E → F) (scale : F → F)
    {x y z : E} {u v : F} (first : u = tap x) (second : v = tap z)
    (hp : x = y) (ht : tap y = scale (tap z)) : u = scale v :=
  first.trans ((congrArg tap hp).trans (ht.trans (congrArg scale second.symm)))

private lemma tapAtZero (L : AC) (e : J!) (x : F!)
    (hx : x 0 ∈ (Drift.Turns D₀ 0).flag e.val) :
    (Drift.Turns D₀ 0).Tap e.val (f' x 0) = (μ e.val)^r • (Drift.Turns D₀ 0).Tap e.val (x 0) :=
  L.tapes e.val e.isLt x 0 (trims.be _) hx

set_option maxHeartbeats 200000 in
lemma pupil (L:AC)(e:J!)(p:U.flag e.val i')(q:U'.flag e.val j')(h:q.val 0=f' p.val 0):
       UΦ Z e.isLt (U'.read e.val e.isLt j' q) 0=(μ e.val)^r • UΦ Z e.isLt (U.read e.val e.isLt i' p) 0:=by
  exact matchPhaseReadouts ((Drift.Turns D₀ 0).Tap e.val) (fun v => (μ e.val)^r • v)
    (vintage Z U' e.isLt j' q 0 (trims.be _)) (vintage Z U e.isLt i' p 0 (trims.be _)) h
    (tapAtZero (hq:=hq) (hz:=hz) (i':=i') (j':=j') a f' L e p.val (U.quake _ e.isLt _ p 0 (trims.be _)).1)
-- payload predicate
abbrev InVivid (e:J!)(x:Mint Z e.val):Prop:=∃ u:U.flag e.val i',∃ w:U'.flag e.val j',f' u.val-w.val∈ Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j' ∧U'.read e.val e.isLt j' w=x
lemma pumpZ (U:Z.Ω M Y)(x:Bead G l e)(h:e<l+1):∃ v:U.flag e i',UΦ Z h (U.read e h i' v) 0=x:=by
       let W:= BoxesΦ Z e h; let p:= W.symm (fun _=> x); obtain ⟨v,hv⟩:= zInvest Z U h i' p; refine ⟨v,?_⟩; rw[hv]; exact congr_fun (W.apply_symm_apply _) _
local notation "Vγ" e:max v:max => InVivid (U:=U) (U':=U') (hz:=hz) (A:=A) (ht:=ht) Z a f' i' j' e v
set_option maxHeartbeats 200000 in
lemma tokensPlus (e:J!)(x y:Mint Z e.val)(hx: Vγ e x)(hy: Vγ e y): InVivid (U:=U) (U':=U') (hz:=hz) (A:=A) (ht:=ht) Z a f' i' j' e (x+y):=by
       obtain ⟨p,q,hp,hq⟩:=hx; obtain ⟨u,v,hu,hv⟩:=hy; refine ⟨p+u,q+v,?_,?_⟩; erw [Submodule.coe_add,Submodule.coe_add,map_add,add_sub_add_comm]; exact Submodule.add_mem _ hp hu
       exact (map_add (U'.read e.val e.isLt j') q v).trans (congrArg₂ (·+·) hq hv)
include hX he
lemma tokensGrow (e:J!)(x:Mint Z e.val)(hx: Vγ e x)(L:AC): Vγ e (WaneZ Z e.val e.isLt x):=by
       obtain ⟨p,q,hp',hq'⟩:= hx; obtain ⟨u,hu,-⟩:=hX.turn e.val e.isLt i' p; obtain ⟨v,hv,hV⟩:=he.turn e.val e.isLt j' q; refine ⟨u,v,?_,hV.trans (congr_arg (WaneZ Z e.val e.isLt) hq')⟩
       rw [hu,hv,L.comm, ← map_sub]; exact sapUp a ht _ (D₀:=D₀) (A:=A j') hp'
end
end YM.OPE.Stroke
