import YM.OPE.Compatible.Hike.Pack
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
abbrev Wings (F:Type):= Fin 3→ F
structure Thruster (g:E≃ₗ[ℝ] Wings F)(S U:E→L[ℝ] E)(qT: ℝ):Prop where
    pitch(x):g (S x) 0=0
    up (i j:Phase) (_he:i.val+1=j.val)(x:E):g (S x) j = g x i
    body(x): g (U x) 0= qT • g x 0
    gauge: S * U= U * S
structure Ding (B:Phase→Dice E)(S:E→L[ℝ] E):Prop where
    ripe(x y:E):
      let W(x y:E):Token:= ⟨B 0 x y,B 1 x y,B 2 x y⟩
      W (S x) y= Ū * W x y ∧ W x (S y)=Ū * W x y
variable {g:E≃ₗ[ℝ] (Fin 3→ F)}{B:Phase→Dice E}{S T:E→L[ℝ] E}
variable (X:Thruster g S T q)(Z:Ding B S)
local notation "SX" i:arg a:arg => g.symm (Pi.single (M:=fun _ : Fin 3=>F) i a)
include X
lemma Thruster.next (x:E)(hp:g x 0=0):∃ z, x=S z:=by
    let y(i:Phase):= if h:i<2 then g x (⟨i.val+1,(by change i.val<2 at h;omega)⟩) else 0; refine ⟨g.symm y,?_⟩; apply g.injective; funext j; fin_cases j; exact hp.trans (X.pitch _).symm
    · have ht:= X.up 0 1 rfl (g.symm y); rw [g.apply_symm_apply] at ht; exact ht.symm
    have ht:=X.up 1 2 rfl (g.symm y); rw [g.apply_symm_apply] at ht; exact ht.symm
lemma Thruster.far (x:E)(hp:g x 0=0)(he:g x 1=0):∃ z,x=S (S z):=by
    obtain ⟨v,rfl⟩:=X.next x hp; rw [X.up 0 1 rfl] at he; obtain ⟨u,rfl⟩:= X.next v he; exact ⟨u,rfl⟩
lemma Thruster.ebb (x:E):g (Ux T q x) 0=0:=by rw [shiftUx,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,X.body,sub_self]
lemma Thruster.rise (x:E)(h:g x 0=0): g (Ux T q x) 1=0:=by obtain ⟨v,rfl⟩:=X.next _ h; rw [show Ux T q (S v)=S (Ux T q v) from ?_,X.up 0 1 rfl]; exact X.ebb v; rw [shiftUx,shiftUx,map_sub,map_smul,show T (S v)= S (T v) from DFunLike.congr_fun X.gauge.symm v]
include Z
lemma Ding.lower (x y:E)(hz:g x 0=0): B 0 x y=0∧B 0 y x=0:=by obtain ⟨v,rfl⟩:= X.next x hz; obtain ⟨h1,-⟩:= Z.ripe v y; obtain ⟨-,h2⟩:=Z.ripe y v; exact ⟨(congr_arg (fun t:Token=>t.seq 0) h1).trans (boneS ..),(congr_arg (fun t:Token=> t.seq 0) h2).trans (boneS ..)⟩
lemma Ding.lows (x y:E)(h:g x 0=0) (hp:g y 0=0): B 1 x y=0:=by obtain ⟨v,rfl⟩:= X.next y hp; obtain ⟨-,hh⟩:= Z.ripe x v; exact (congr_arg (fun t:Token=> t.seq 1) hh).trans ((boneL ..).trans (show _ from (Z.lower X x v h).1))
lemma Ding.upper (x y:E)(h:g x 0=0)(hp:g x 1=0): B 1 x y=0 ∧ B 1 y x=0:=by obtain ⟨v,rfl⟩:= X.far x h hp; obtain ⟨hx,-⟩:=Z.ripe (S v) y; obtain ⟨-,hy⟩:= Z.ripe y (S v); obtain ⟨hg,hq⟩:= Z.lower X (S v) y (X.pitch v); exact ⟨(congr_arg (fun t:Token=> t.seq 1) hx|>.trans ((boneL ..).trans hg)), (congr_arg (fun t:Token=> t.seq 1) hy |>.trans ((boneL ..).trans hq))⟩
end general
end YM.OPE.Quit.Jac
