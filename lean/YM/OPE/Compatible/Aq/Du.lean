import YM.OPE.Compatible.Aq.Hack
/-!
# Phase thresholds and patch order

`YM.OPE.Stroke.Coach` packages a patch whose side is a power of three, its phase thresholds, and the bounds needed for its OPE data.
For a simple gauge group and a `PriceBook`, `behaviors` constructs this data at any patch order `p ≥ max 5 (l + 3)` when `l ≤ d`.
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
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}
lemma mindful (d k:ℕ):∃ τ:Phase→ℕ,Aware d τ ∧∀ i,k≤ τ i:=by
     let z:= k+2*(d+4)+45; refine ⟨![z+4*(d+4)+2,z+2*(d+4)+1,z], ?_,?_⟩
     · constructor <;> intros
       · rename_i i; fin_cases i <;>dsimp [z] <;> omega
       rename_i i j h; fin_cases i <;> fin_cases j <;> (first | (exfalso; revert h; decide) | (dsimp [z]; omega))
     intro i; fin_cases i <;> dsimp [z] <;> omega
-- bundle parameters.
structure Coach (H:LocalRatio R)(L:PriceBook H T)(hs:G.Simple)(l d k:ℕ) where
     J : ℕ
     S : Patch
     crisp : S.L=(3:Side)^J
     τ : Phase→ℕ
     hτ : Aware d τ
     holds i : Rise.stamp' d G k+44 ≤ τ i
     receives i : Variance.StencilTax d k ≤ τ i
     tally : l*l ≤ τ 0
     Medal₂ : Medal S G K.K S.J
     HopeZ : ℝ
     stars : Stern K S τ l d HopeZ
     p : Clip
     ho : p.direct ≤ K.γ S.J
     q : Quota K T S.J S.J
     hq : q.minL ≤ S.L.val
     X : Sailing T S p R (big_cost q S.L)
     sign : Lance X
     m : ℕ
     hp i : τ i ≤ m
     Glp : Alps.Crest G S K.K m
     Z : Topic H hs X Medal₂ stars
lemma behaviors (L:PriceBook H T)(l d k:ℕ)(p:ℕ)(hp:max 5 (l+3)≤p)(hd:l≤d):∃ C:Coach H L hs l d k, C.S.J=p:=by
     obtain ⟨τ,hτ,hZ⟩:= mindful d (l*l+(Rise.stamp' d G k+44)+Variance.StencilTax d k); let m:=τ 0; have hz: τ 0≥3:=by have h:=hτ.credit 0; omega
     obtain ⟨v,i,he⟩:= Drift.rally K p hd ((le_max_right ..).trans hp) (by omega) hτ; obtain ⟨j,hj⟩:= Votive.Alps.patroness G K.K p m (by omega) hz
     obtain ⟨U⟩:= L.g p; let Q:Patch:=⟨(3:Side),p,by omega,by decide, ⟨1,rfl⟩⟩; obtain ⟨u,h,hg,hh⟩:= widens Q (max i (max j U.minL)); let S:Patch:=⟨Q.L^u,p,by omega,hh,hg⟩; have hv:U.minL ≤ S.L.val:=le_trans (le_max_right ..) ((le_max_right ..).trans h); obtain ⟨q,hq⟩:= tyre K p; have hY:Stern K S τ l d v:= he _ ((le_max_left ..).trans h) hh hg; have hy: Crest G S K.K m:= hj _ ((le_max_left ..).trans ((le_max_right ..).trans h)) hg hh
     obtain ⟨X,hX⟩:= L.launch S q U hq hv; obtain ⟨B⟩:= medal_buy hg (K.affordable S) S.order_cut; have hx(i:Phase): τ i ≤ m:= hτ.mono (Fin.zero_le i); obtain ⟨Z⟩:= (arises (X:=X) (H:=H) (B:=B) (hs:=hs) (D₀:=hY) hy hx); exact ⟨⟨u,S,rfl,τ,hτ,fun i=>by have h:=hZ i; omega,fun i=>by have h:=hZ i; omega,by have h:=hZ 0; omega,B,v,hY,q,hq,U,hv,X,hX,m,hx,hy,Z⟩,rfl⟩
end YM.OPE.Stroke
