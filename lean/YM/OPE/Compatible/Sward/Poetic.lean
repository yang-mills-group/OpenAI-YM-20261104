import YM.OPE.Compatible.Sward.Forge
/-!
# Warmup all stages once purchased. Advances. -/
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
variable (Q':Quota K T P.J P.J)(N: Q'.minL≤P.L.val)(b':big_cost Q' P.L≤ b)(Qh:p.direct ≤ K.γ P.J)
variable (hB:l+l<k)(hL:∀ i,τ i≤m)(ha:∀ i,Rise.stamp' d G k+44 ≤ τ i)(h:∀ i,Variance.StencilTax d k ≤ τ i)
include N b' Qh hB hL ha h
lemma patrolS (hq:∀ i,Nonempty (Quota K T (i+1) i))(Q:ℕ)(ht:P.J≤Q) :∀ (p':Clip)(Y:M→ℝ)(A:(i:M)→ Alps K T Q (Y i))(hP:1 ≤Y), (∀ i,(A i).clip=p')→∃ W:Z.Ω M Y,Z.Floss A W (P.order_cut.trans ht) (le_trans zero_le_one hP) k Hp a∧Z.Stone Y W:=by
       induction Q, ht using Nat.le_induction with
       | base=> intro p' Y A hP H; exact Molt Hp Z a Q' N b' Qh hB hL ha h A hP H
       | succ n hn IH=>
         intro p' Y A hP Ht; obtain ⟨D⟩:= hq n; obtain ⟨i,he,hV,hv⟩:= widens P D.minL; let P':Patch:=⟨P.L^i,n+1,P.order_cut.trans (le_trans hn (Nat.le_succ _)),hv,hV⟩; have hp:Mag P'.J n:=⟨P'.order_cut,P.order_cut.trans hn,Or.inr rfl⟩; obtain ⟨p,hp'⟩:= tyre K n; obtain ⟨U,hY,hζ,_,t,hU,Zη,hZ⟩:= cashDay (P':=P') D 0 A hP hp hp' he H
         obtain ⟨V,hV,hσ⟩:= IH p U Zη hY (fun i=>(hZ i).1); obtain ⟨B⟩:= medal_buy P'.odd_side (K.affordable P') P'.order_cut; exact raiseS (P:=P) Hp Z a A B Zη hP (le_trans zero_le_one hY) hζ hU Ht (by change l+1≤ n+1; have he:=D₀.oak; omega) (r:=i) rfl hp (fun i=>(hZ i).2) V hV hσ
end YM.OPE.Stroke
