import YM.OPE.Compatible.Rave.Tara
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
lemma Thruster.feel (x:E)(i:ℕ): g ((T^i) x) 0= q^i • g x 0:=by induction i with
   | zero=>simp
   | succ i ih=> rw [pow_succ',byway,X.body,ih,smul_smul,pow_succ']
-- Ux for Cord curvature ν.
variable {hK:0<q}
include Z
lemma Ding.slice {x x' y y':E}(h:g x 0=g x' 0)(hx:g y 0=g y' 0):B 0 x y=B 0 x' y':=by have hA := (Z.lower X (x-x') y (by rw [map_sub,Pi.sub_apply,h,sub_self])).1; have hV:= (Z.lower X (y-y') x' (by rw [map_sub,Pi.sub_apply,hx,sub_self])).2; exact (sub_eq_zero.mp (by rw [map_sub] at hA; exact hA)).trans (sub_eq_zero.mp (by rw [map_sub] at hV; exact hV)) -- expand
lemma turbine0 (x y:E)(i:ℕ): B 0 ((T^i) x) ((T^i) y)= (q*q)^i*B 0 x y:=by
    have he(x:E): g ((T^i) x) 0=g (q^i • x) 0:=by rw [X.feel,map_smul];rfl
    rw [Z.slice X (he x) (he y),map_smul,map_smul,_root_.smul_apply,mul_pow]; change q^i*(q^i*_) = _; ring
abbrev Spice (q:ℝ)(T:E→L[ℝ] E)(B:Phase→Dice E)(x y:E):ℝ:= B 1 (Ux T q x) y + B 1 x (Ux T q y)
lemma splice_eq (x y:E) (i:ℕ): Spice q T B ((T^i) x) ((T^i) y)=(q*q)^i* Spice q T B x y:=by
     have he(p q' r s:E)(hp:g p 0=0)(h:g r 0=g s 0)(hh:g q' 0=0)(hx:g p 1=g q' 1): B 1 p r=B 1 q' s ∧ B 1 r p=B 1 s q':=by
          have hX:g (p-q') 0=0:=by rw [map_sub,Pi.sub_apply,hp,hh,sub_zero]
          have hP:g (r-s) 0=0:=by rw [map_sub,Pi.sub_apply,h,sub_self]
          obtain ⟨hy,hY⟩:= Z.upper X (p-q') r hX (by rw [map_sub,Pi.sub_apply,hx,sub_self]); have ha:=Z.lows X q' (r-s) hh hP; have hb:= Z.lows X (r-s) q' hP hh
          rw [map_sub] at hy hY ha hb; exact ⟨(sub_eq_zero.mp hy).trans (sub_eq_zero.mp ha),(sub_eq_zero.mp hY).trans (sub_eq_zero.mp hb)⟩
     have hg(v:E): g ((T^i) v) 0=g (q^i • v) 0:=by rw [X.feel,map_smul];rfl
     have hA(u v:E): let p:=Ux T q ((T^i) u); let r:=q^i • (Ux T q u); B 1 p ((T^i) v)= B 1 r (q^i • v)∧ B 1 ((T^i) v) p=B 1 (q^i • v) r:=by
          intro p r; refine he p r _ _ (X.ebb _) (hg v) (by unfold r; rw [map_smul,Pi.smul_apply,X.ebb,smul_zero]) ?_; let V:= Ux T q; apply sub_eq_zero.mp; have ht:g ((T^i) u-q^i • u) 0=0:=(by rw [map_sub,Pi.sub_apply,hg,sub_self]); have h:= X.rise ((T^i) u-q^i • u) ht; rw [map_sub,map_smul,map_sub,Pi.sub_apply] at h; exact h
     unfold Spice; rw [(hA x y).1,(hA y x).2]; simp only [map_smul,_root_.smul_apply,smul_eq_mul,mul_pow];ring
lemma turbine1 (x y:E)(i:ℕ)(hp:0<q): B 1 ((T^i) x) ((T^i) y)=(q*q)^i * (B 1 x y + (i:ℝ)*(q⁻¹*Spice q T B x y)):=by
   have he(x y:E): B 1 (T x) (T y)=q*q*B 1 x y+q*Spice q T B x y:=by
         let a:=B 1; let L:=Ux T q; have hv(i:E): T i=q • i+L i:=by rw [show L i=_ from (shiftUx T q i)]; abel
         rw [hv x,hv y]; have hp:= Z.lows X (L x) (L y) (X.ebb _) (X.ebb _); simp only [map_add,_root_.add_apply,map_smul,_root_.smul_apply,smul_eq_mul,hp]; unfold Spice; unfold L;ring
   induction i with
   | zero=>simp
   | succ i ih=> rw [pow_succ' T,byway, byway, he, ih, splice_eq X Z, pow_succ]; push_cast; field_simp; ring
end general
end YM.OPE.Quit.Jac
