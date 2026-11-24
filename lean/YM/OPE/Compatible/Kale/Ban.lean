import YM.OPE.Compatible.Kale.Gpx
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
local notation "Z"=> solar G d τ
variable (H:Even c.val) (X:Plot H){A:Alps K T i v}
local notation "V"=> Libra.Keys G (Limb H)
local notation "E'"=> Libra.Keys G (Stand.Free X)
variable (Vj:Bor H A b)
local notation "o¤"=> penon (Vj.L X)
include Vj
open JetS Pose
lemma receipt (v:E')(u:ℝ): jet (haloP u A) 2 (rayS H X G v)= -u*((o¤).P v v/2) -jet (swornY A.live (n:=c)) 2 (rayS H X G v)/4 :=by
   rw [← penon_shape,cargo H X Vj v 2 (by decide)]
   let D:=swornV A.clip A.live (n:=c); let Y:=swornY A.live (n:=c); have hv:ContDiffAt ℝ ω D 0:= (chartK A.live A.clip c A.pays).1; have hy:ContDiffAt ℝ ω Y 0:= (tubesY A.live A.clip c A.pays).1
   let x:=rayS H X G v; let a:=(-u) • D; let g:=(-1:ℝ) • Y; have ha:ContDiffAt ℝ ω a 0:= hv.const_smul (-u); have hb:ContDiffAt ℝ ω g 0:=hy.const_smul (-1:ℝ); change jet ((4:ℝ)⁻¹ • (a+g)) 2 x= -u*(jet D 2 x/4)-jet Y 2 x/4; rw [arcConst _ (f:=a+g) ((ha.add hb).of_le le_top),arcAdd (f:=a) (g:=g) (ha.of_le le_top) (hb.of_le le_top), show jet a 2 x=_ from arcConst (-u) (hv.of_le le_top) x,show jet g 2 x= _ from arcConst (-1:ℝ) (hy.of_le le_top) x]; ring
variable (W': Bor H A v')
local notation "δ"=> (v'-b)
lemma cashUp (p:E')(hr:LocalRatio R)(hs:G.Simple): (W'.L X).hat R p=(Vj.L X).hat R p+ merry (0 - δ*(o¤).P p p/2):=by
     rw [SwiftD H X W' hr hs,SwiftD H X Vj hr hs]; dsimp only; rw [receipt H X Vj p v', receipt H X Vj p b]; unfold merry flareTok; apply eta <;> simp ; ring
omit Vj in
noncomputable def Tru (G:Gauge)(h:Aware d τ)(p:solar G d τ)(b:ℝ): solar G d τ:=⟨rebase G h b p.val, aboard b h p.val p.property⟩
omit Vj in
lemma interchangeE (x:Site c)(y:E')(a:Tower (Shade G) d τ)(h: Aware d τ)(b:ℝ):
      let f:= X.charted (cutφ H a x)
      X.charted (cutφ H (rebase G h b a) x) y=f y+merry ((b/2)* Pose.hillP (fun i=>(f i).s) y):=by
         intro f
         let R(u:Bid.Dir G c):= (Vtap a x u).s; let T:= rayS H X G; have ht(y:E'):(f y).s=R (T y):=rfl; rw [show X.charted (cutφ H (rebase G h b a) x) y= _ from (show Vtap (rebase G h b a) x (T y)= _ from Drift.flot a h b (T y) x)]; change f y+⟨_,_,(b/2)*deriv (fun i:ℝ=>R (i • T y)) 1⟩=_; simp_rw [← map_smul T,←ht]; have hh:Bond R:= meridian (spread G d τ a) _ 0 _ _ (resin a (fun i=>Nat.zero_le _)) 0; rw [orbitD (q:=fun i=>(f i).s) (p:=y) (show _ from hh.compLinear T.toLinearMap)] -- names
omit Vj in
lemma isoBack (p q:Z)(h:Aware d τ)(x y:Site c)(w:E')(v:ℝ):
    let f:=isolate H X p.val q.val x y; isolate H X (rebase G h v p.val) (rebase G h v q.val) x y w=f w+ merry ((v/2)*hillP (fun i=>(f i).s) w):=by
       intro f
       let P:= X.charted (cutφ H p.val x); let Q:= X.charted (cutφ H q.val y)
       let a(i:E'):= (P i).s; let b(i:E'):= (Q i).s
       have hv(i:E'):(f i).s= a i*b i:= JetS.ml_s _ _
       have hp: Differentiable ℝ a:= ((X.composeWard (CloudH H p x) 0).smooth).differentiable (by simp); have hq: Differentiable ℝ b:= ((X.composeWard (CloudH H q y) 0).smooth).differentiable (by simp)
       change X.charted (cutφ H _ x) w* X.charted (cutφ H _ y) w= P w* Q w+_
       rw [interchangeE H X x w p.val h,interchangeE H X y w q.val h]; let u:= v/2; change (P w+merry (u*hillP a w))*(Q w+merry (u*hillP b w))=_; rw [show (fun i=>(f i).s)=a*b from rfl]; unfold hillP merry; rw [fderiv_mul (hp w) (hq w)]; apply eta <;> simp ; ring
lemma ledgers (p q: Z)(x y:Site c)(h:LocalRatio R)(hs:G.Simple)(H':Aware d τ):
   RGram H X W' (Tru _ H' p δ) (Tru _ H' q δ) x y R= RGram H X Vj p q x y R:=by
        let P:= penon (Vj.L X); let A:= Vj.L X; let B:= W'.L X; let μ:= Chart.tangent G X.Free; have he:penon A=penon B:=real_law H X Vj W'
        unfold RGram;rw [Lid.cutOut _ h _ _ (penon_shape A), Lid.cutOut _ h _ _ (penon_shape B), ← real_law H X Vj W']; let C':= isolate H X p.val q.val x y; let g(v:E'):=(δ/2)*hillP (fun v => (C' v).s) v; let D:= isolate H X ((Tru _ H' p δ).val) ((Tru _ H' q δ).val) x y; change fair μ P (B.hat R) D = fair μ P (A.hat R) C'; have hp:= isolateB H X p q x y; rw [show B.hat R= _ from funext fun i=> cashUp H X Vj W' i h hs, show D=fun j=>C' j+merry (g j) from funext fun i=>isoBack H X p q H' x y i δ]; rw [rental μ P (A.hat R) C' _ g δ 0 (A.hat_toll h) hp (Bond.scale _ (heatE (hp 0))) (fun _=>rfl) (A.hat_full h)]; rw [show P.average μ g= (δ/2)*P.average μ (hillP (fun v=>(C' v).s)) from scooted ..,sub_self]; exact add_zero _
end YM.OPE.Quit
