import YM.OPE.Compatible.Kash.Frieze
import YM.OPE.Compatible.Kash.Trill
import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
section
variable {v c:Side}(h:c.val ∣ n.val)(e:RootEdge)(u:G.ColorIndex)(X:Bid.Dir G c)(x:Site n)
local notation "θ"=> trimT n c h
local notation "W"=> Booklet h G
local notation "ξ"=> trimT n c h x
variable {K:Sponsor G}{T:Seasons K}(A:Alps K T i t)
lemma GoalP (a:G.Color)(b:Bool)(f:ScriptJ (Bid.Dir G n))(g:ScriptJ (Bid.Dir G c))(hp:∀ j:G.ColorIndex, Pry (functorE x e j) f (W X)=Pry (functorE (θ x) e j) g X): Topper (sett n x e) a b f (W X)=Topper (sett c (θ x) e) a b g X:=by
       unfold Topper Flux; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> congr_arg₂ (·*·) (mountYield h e i X x a b) (hp i)
variable [Fintype I] (p:I→RootEdge)(k:ℕ)(b:Bool)(P:Libra.Keys G I→G.Color)(hP:ContDiffAt ℝ ω P 0)(ht:0≤t)(hc:Anti c e p)
include ht hc hP
lemma retro : Cake (sett n x e) b (Dune A) (Rh A) (P∘ dip p n x) k (W X)= Cake (sett c (θ x) e) b (Dune A) (Rh A) (P∘ dip p c (θ x)) k X:=by
       let F(i:G.ColorIndex):= (Phone G).coord i ∘ P; have hp(i): ContDiffAt ℝ ω (F i) 0:= (((Phone G).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp _ hP)
       unfold Cake; rw[Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i _
       let f(n:Side)(x:Site n):= Pawn.mold (F i ∘ dip p n x) k; let z(n:Side):= Pawn.mold (Dune A (n:=n)) 2 + Pawn.mold (Rh A (n:=n)) 0; let v(n:Side)(x:Site n):= Topper (sett n x e) (Phone G i) b
       change v n x (z n) (W X)* f n x (W X)-v n x (f n x) (W X)= v c ξ (z c) X * f c ξ X-v c ξ (f c ξ) X
       have hv(a) := PayMask h e a X x p k (F i) (hp _) hc; rw [show v n x (f n x) (W X)= _ from GoalP h e X x _ b _ _ hv, show f n x (W X) =_ from mouldYield h X x p k _ (hp i)]; apply congr_arg (· - _); apply congr_arg (· * _); apply GoalP h e; intro u; unfold z; rw [pryAdd _ _ _ (tallJ _ _) (tallJ _ _),pryAdd _ _ _ (tallJ _ _) (tallJ _ _)]; exact congr_arg₂ (·+·) (heave h e u X x A 1) (slotsV h e u X x A ht)
variable {τ:Phase→ℕ}(Q:solar G d τ)
lemma terroir (hz:∀ᶠ n:Side in atTop,∀ (x:Site n),mind Q.val n x=Cake (sett n x e) b (Dune A) (Rh A) (P∘ dip p n x) k) (x:Site c): mind Q.val c x=Cake (sett c x e) b (Dune A) (Rh A) (P∘ dip p c x) k:=by
       obtain ⟨s,hs⟩:= eventually_atTop.mp hz; let i:=c*s; have hv:s ≤ i:= Nat.le_mul_of_pos_left _ c.pos; let v:=wrap i (lift x); have he:c.val∣ i.val:= dvd_mul_right ..; have hp:trimT i c he v=x:= (lease ..).trans (wrap_lift x); funext u; have hU:= congr_fun (hs i hv v) (Booklet he G u); have hV:= retro he e u v A p k b P hP ht hc; rw [hp] at hV; exact (congr_arg (fun y=> mind Q.val c y u) hp.symm).trans ((labRel ..).symm.trans (hU.trans hV))
end
end YM.OPE.Variance
