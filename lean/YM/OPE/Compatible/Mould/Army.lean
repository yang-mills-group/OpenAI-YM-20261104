import YM.OPE.Compatible.Mould.Parm
/-!
# Stem extension.Killer lift -/
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
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J}{w:ℝ}{D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full
variable {p₁:Clip}{u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(L:Lance X)
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
local notation "F!"=>Tracts G d τ
local notation "D!"=>Topic.Dross Hp Z a e
include L T' hq
set_option maxHeartbeats 200000 in
lemma summons (he:e<l+1)(hx:HostE e ν U (Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)))(hz:0≤ν) : SonE e he ν U S! (Topic.Dross Hp Z a e):=by
     intro p hy hF j hj ht r hP; let Y:=Mint Z e; let P(y:Mint Z e):=LimitQ (UΦ Z he y 0) r; let W(m):= Sapling (V:=V) (D₀:=D₀) (a:=a) m (H:=H) (hs:=hs) (hp:=hp) (hq:=hq); let A:=Topic.Dross Hp Z a e
     have H(y:Mint Z e)(i:M)(q:U.flag e i)(h:P y)(hz:Crop r q.val): P (y-U.read e he i q):=by unfold P; rw [phiSub,discU he]; exact LimitQ.Drop h (fringP D₀ _ he hz)
     have h(x:M→Z.Mint e)(hX:Wealth (fun i:M=>(x i:Mint Z e).val) u ν)(hy:∀ i,x i∈A)(hΦ:∀ i,P (x i))(j:Phase)(ht:∀ i,trims j.val (x i).val):∃ f:∀ i,U.flag e i, Wealth (fun i=>(f i).val) u ν∧(∀ i,(f i).val∈ W i) ∧∀ i,trims j.val (f i).val∧ Crop r (f i).val ∧ trims (j.val+1) (x i-U.read e he i (f i)).val:= stepCut (hq:=hq) Hp T' L hx x hX j ht hy hΦ
     exact U.Decks A W he hz P (Crop r) (Crop.from rfl) (fun _ _ h hx => Crop.plus h hx) (fun i t hv=>stockMe Hp T' i t hv) H h p hy hF hP j hj ht
end YM.OPE.Stroke
