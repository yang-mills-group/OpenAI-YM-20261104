import YM.OPE.Compatible.Sward.Can
/-!
# Phase cutoffs at a prescribed patch order

For `max 5 (l + 3) ≤ p` and `l ≤ d`, `behaviorX` constructs a `Coach`
whose patch has order `p`. Its phase cutoffs satisfy `Aware (d + 2)`
and exceed or equal the requested lower bound at every phase.
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
lemma Awake_more {n k:ℕ}(h:Aware n τ)(ht:k ≤ n):Aware k τ:=by
     refine ⟨fun i=>?_,fun i j he=>?_⟩
     · have ht:=h.credit i; omega
     have hh:=h.margin i j he; omega
lemma behaviorX (R0:ℕ) (L:PriceBook H T)(l d k:ℕ)(p:ℕ)(hp:max 5 (l+3)≤p)(hd:l≤d):∃ C:Coach H L hs l d k, C.S.J=p ∧ Aware (d+2) C.τ ∧∀ i,R0 ≤ C.τ i:=by
     obtain ⟨τ,hU,hZ⟩:= mindful (d+2) (l*l+(Rise.stamp' d G k+44)+Variance.StencilTax d k+R0); have hτ:=Awake_more hU (Nat.le_add_right d 2); let m:=τ 0; have hz: τ 0≥3:=by have h:=hτ.credit 0; omega
     obtain ⟨v,i,he⟩:= Drift.rally K p hd ((le_max_right ..).trans hp) (by omega) hτ; obtain ⟨j,hj⟩:= Votive.Alps.patroness G K.K p m (by omega) hz
     obtain ⟨U⟩:= L.g p; let Q:Patch:=⟨(3:Side),p,by omega,by decide, ⟨1,rfl⟩⟩; obtain ⟨u,h,hg,hh⟩:= widens Q (max i (max j U.minL)); let S:Patch:=⟨Q.L^u,p,by omega,hh,hg⟩; have hv:U.minL ≤ S.L.val:=le_trans (le_max_right ..) ((le_max_right ..).trans h); obtain ⟨q,hq⟩:= tyre K p; have hY:Stern K S τ l d v:= he _ ((le_max_left ..).trans h) hh hg; have hy: Crest G S K.K m:= hj _ ((le_max_left ..).trans ((le_max_right ..).trans h)) hg hh
     obtain ⟨X,hX⟩:= L.launch S q U hq hv; obtain ⟨B⟩:= medal_buy hg (K.affordable S) S.order_cut; have hx(i:Phase): τ i ≤ m:= hτ.mono (Fin.zero_le i); obtain ⟨Z⟩:= (arises (X:=X) (H:=H) (B:=B) (hs:=hs) (D₀:=hY) hy hx); exact ⟨⟨u,S,rfl,τ,hτ,fun i=>by have h:=hZ i; omega,fun i=>by have h:=hZ i; omega,by have h:=hZ 0; omega,B,v,hY,q,hq,U,hv,X,hX,m,hx,hy,Z⟩,rfl,hU, fun i=> by have hh:= hZ i; exact le_trans (Nat.le_add_left ..) hh ⟩
end YM.OPE.Stroke
