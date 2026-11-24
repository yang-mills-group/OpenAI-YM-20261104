import YM.OPE.Compatible.Clove.Host
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
namespace Scape
variable {W:Type}{nρ fρ:W→Side}(U:(x:W)→ Scape K T P (nρ x) (fρ x) i j R) {u m₁ m₂ m₃ w:ℝ}{q:W→ℝ}{s:ℕ}
local notation "Σ(" i ")"=> VC (U i)
local notation "L!"=> solar G d τ

local notation "σ!"=> gDump nρ k
lemma cupDiff (x y:Token)(i:Phase):(x-y).seq i.val=x.seq i.val-y.seq i.val:=by fin_cases i<;>rfl
lemma dutyT (S:SlopePrice U k u m₁ w)(pW:LocalRatio R)(hs:G.Simple)(h: Aware d τ)(hx:∀ i,k+44 ≤ τ i)(x:W→L!) (a:(i:W)→Site (nρ i)): WindT nρ 0 (glideZ d) (passM x*σ!) ((fun i=>MuseIn U i x a)-(fun i=>MuseOut U i x a hs pW h)):=by
   obtain ⟨c,hc,H⟩:=rampOne U S hs pW h hx x a; intro j; let Op(i):= (U i).upL hs pW h (x i); refine ⟨⟨c,hc,fun i v=>?_⟩,fun i=>?_⟩; swap
   · let N: Bond (fun v=> (MuseIn U i x a v).seq j.val):= poolB _ pW (blotS _ _ _) j.val; let u:= (Op i); let V:= U i; have hu: Bond (fun v=> (MuseOut U i x a hs pW h v).seq j.val):=Stand.composeWard V.E (CloudH V.tH u (a i)) j.val; let R:= N.sub hu; simpa only [Pi.sub_apply,cupDiff] using! R -- find lemma
   specialize H i v j; simp only [Pi.sub_apply,cupDiff,care,pow_zero, Pi.mul_apply]; exact gWorry _ _ _ _ _ k H -- p vsR params

lemma Magn (pW:LocalRatio R)(hs:G.Simple)(h: Aware d τ)(x:W→L!) (a:(i:W)→Site (nρ i))(Z:ℝ)(hp:∀ i,‖(U i).vault hs pW h‖ ≤ Z): WindT nρ 0 (glideZ d) (passM x) fun i=>MuseOut U i x a hs pW h:=by
    let p(i):=(U i).upL hs pW h (x i); have hx: WindT nρ 0 (d+2) (passM p) fun i=> MuseOut U i x a hs pW h:= earM p _ (fun i=>(U i).tH) (fun i=>(U i).E) a; let f:=fun i=> MuseOut U i x a hs pW h; have hp(i):‖p i‖≤ max 0 Z*‖x i‖:=by apply ((U i).vault hs pW h).le_opNorm _|>.trans; exact mul_le_mul_of_nonneg_right ((hp i).trans (le_max_right ..)) (norm_nonneg (x i))
    refine WindT.gauge ?_ (fun i=>norm_nonneg (x i)) le_rfl (le_refl _) (show d+2≤glideZ d by unfold glideZ;omega); intro i; obtain ⟨c,hc,H⟩:= (hx i).cap; refine ⟨⟨c*max 0 Z,mul_nonneg hc (le_max_left ..),fun j v=> (H j v).trans ?_⟩,(hx i).zon⟩; unfold care passM; simp only[pow_zero,one_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hp j) (by positivity)) hc); exact le_of_eq (by ring)
lemma crownP (S:SlopePrice U k u m₁ w)(pW:LocalRatio R)(hs:G.Simple)(h: Aware d τ)(hx:∀ i,k+44 ≤ τ i)(x:W→L!) (a:(i:W)→Site (nρ i))(Z:ℝ)(hp:∀ i,‖(U i).vault hs pW h‖ ≤ Z): WindT nρ 0 (glideZ d) (passM x) fun i=> MuseIn U i x a:=by
      let P:= (fun i=>MuseIn U i x a); let E:=fun i=>MuseOut U i x a hs pW h; have hv :0 ≤ passM x:=fun i=> norm_nonneg _; have hh:WindT nρ 0 (glideZ d) (passM x) (P-E):=WindT.gauge (dutyT U S pW hs h hx x a) (fun i=>mul_nonneg (hv i) (gDuty _ _ i)) (fun i=>mul_le_of_le_one_right (hv i) (gLow _ _ i)) le_rfl le_rfl; change WindT _ _ _ _ P; rw [show P=P-E+E from (sub_add_cancel ..).symm]; exact hh.add (Magn U pW hs h x a Z hp)
lemma PaidEcho (S:SlopePrice U k u m₁ w)(pW:LocalRatio R)(hs:G.Simple)(h: Aware d τ)(hx:∀ i,k+44 ≤ τ i)(x y:W→L!) (a b:(i:W)→Site (nρ i))(Z:ℝ)(hp:∀ i,‖(U i).vault hs pW h‖ ≤ Z)(t':ℝ)(he:2 ≤ t')(hh:∀ i, Settle (a i) (b i) t'):
    let _X(i):=MuseIn U i x a
    let _Y(i):=MuseIn U i y b
    let g(i):= MuseJ U i x y a b
    let k(i):= isolate (U i).tH (U i).E ((U i).upL hs pW h (x i)).val ((U i).upL hs pW h (y i)).val (a i) (b i)
    WindT nρ 0 (glideZ d+glideZ d) (passM x*passM y*σ!) (g-k):=by
       intro X Y g t; let p:= passM x*passM y*σ!; have hv: WindT nρ 0 (glideZ (d+d)) p (g-X*Y):=growStuff U hs pW hx x y a b t' he hh S; have hX:0 ≤ passM x:=fun _=> norm_nonneg _; have hY:0 ≤ passM y:=fun _=> norm_nonneg _; have hb:0≤σ!:= gDuty _ _; have hA:= hX; let A':=fun i=>MuseOut U i x a hs pW h; let B':=fun i=> MuseOut U i y b hs pW h
       rw [show g-t=(g-X*Y)+ (X-A')*Y+A'*(Y-B') from ?_]; rotate_left
       · rw [show t=A'*B' from rfl,sub_mul,mul_sub]; abel
       refine ( ((WindT.gauge hv (fun i=>mul_nonneg (mul_nonneg (hX _) (hY _)) (hb _)) le_rfl le_rfl (show glideZ (d+d) ≤ _ from by unfold glideZ;omega)).add ?_).add ?_); swap
       · convert! (WindT.prod (Magn U pW hs h x a Z hp) (dutyT U S pW hs h hx y b) hX) using 1; exact mul_assoc ..
       convert! (WindT.prod (dutyT U S pW hs h hx x a) (crownP U S pW hs h hx y b Z hp) (fun i=>mul_nonneg (hX _) (hb _))) using 1; exact mul_right_comm ..
end Scape
end YM.OPE.Quit.PriceZ
