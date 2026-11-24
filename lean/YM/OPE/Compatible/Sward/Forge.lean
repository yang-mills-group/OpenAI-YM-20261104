import YM.OPE.Compatible.Sward.Vore
import YM.OPE.Compatible.Roost.Romance
import YM.OPE.Compatible.Roost.Note
/-!
# Starting levels. Prog uniform rails. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)
variable (Z:Topic H hs X B D₀)(a:Axis)
variable {Y Y' α:M→ℝ}
lemma raiseS (A:(j:M)→Alps K T P'.J (Y j))(B':Medal P' G K.K P'.J)(V:(w:M)→Alps K T j (Y' w))(hx:1 ≤ Y) (hv:0 ≤Y')(ht: Wealth Y' Y 1)(hV:Wealth α Y 1)(hh:∀ i, (A i).clip=p')(hQ:l+1 ≤ P'.J)(hR:P'.L=P.L^r)(hg:Mag P'.J j)(hl:∀ i, Charm P'.L (A i) (V i) (α i) R)(U:Z.Ω M Y')(p:Z.Floss V U hg.2.1 hv k Hp a)(e:Stone Z Y' U) : ∃ W:Z.Ω M Y, Z.Floss A W P'.order_cut (le_trans zero_le_one hx) k Hp a∧ Z.Stone Y W:=by
      let F(i):= spots H B' (A i) (V i) (hl i); have hT : Wealth (fun i=> MotionX H hs (F i) D₀.aware P'.order_cut hg.2.1) Y 1:= MotionFee H hs A B' D₀.aware _ hh _ V F hx hV; have hS:=motionAd H hs D₀ A V hg hl B' (le_trans zero_le_one hx) hv hR hQ p.vol p.dimD a; refine ⟨_, Extens Hp Z hS hx U ht hT p, fun i p hx=>?_⟩
      change (MotionX H hs (F i) D₀.aware P'.order_cut hg.2.1 p)∈U.flag (l+1) i; apply e i _; let t:= iotaK P' hg (A i).gear; exact Silt.Phere.matelot H t (A i) (V i) B' D₀.aware hg rfl p (endV _ _ hg (hl i)) hs (F i) hx
variable (Q':Quota K T P.J P.J)(N: Q'.minL≤P.L.val)(b':big_cost Q' P.L≤ b)(Qh:p.direct ≤ K.γ P.J)
variable (hB:l+l<k)(hL:∀ i,τ i≤m)(ha:∀ i,Rise.stamp' d G k+44 ≤ τ i)(h:∀ i,Variance.StencilTax d k ≤ τ i)
include N b' Qh hB hL ha h
lemma Molt (A:(i:M)→Alps K T P.J (Y i))(hv:1 ≤Y)(hx: ∀ i,(A i).clip=p') :∃ W:Z.Ω M Y,Z.Floss A W P.order_cut (le_trans zero_le_one hv) k Hp a∧ Z.Stone Y W:=by
      have hh:Mag P.J P.J:= ⟨P.order_cut,P.order_cut,Or.inl rfl⟩; obtain ⟨V,h₁,h₂,h₃,z,hz,x,Hx⟩:= cashDay (p:=p) Q' (Q'.tab P.L) A hv hh Qh N H -- P := implicit
      obtain ⟨C,hC,hp⟩:= growL (P:=P) Q' x h₁ (fun i=>(Hx i).1) Qh N b' h₃ H; subst V; let y(i:M):= (C i).U 0; have he:x=y:=funext (fun i=>Eq.symm (eq_of_heq (hp i))); let Q:= Edel Hp Z hB hL ha h a; have hY:= Floss.pullAlong Hp Q C; apply raiseS (p':=p') Hp Z a A B y hv (le_trans zero_le_one h₁) h₂ hz hx (by have hh:=D₀.oak;omega) (pow_one P.L).symm hh (fun i=>he ▸ (Hx i).2) (Z.Wb.branch C) hY
      exact fun i p hx=> budK _ (C i) p hx
end YM.OPE.Stroke
