import YM.OPE.Compatible.Streams.Ride
/-! # H beam through stand within register.Q charges clipped on stamps -/
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
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier
variable {u d s r l k m:ℕ}{W I:Type}{τ:Phase→ℕ}
variable {K:Sponsor G}{S:Seasons K}{t:ℝ}(A: Alps K S s t)(hp:4 ≤ s)(hs:G.Simple)(hr:LocalRatio P)(hv:0 ≤ t)
section price
variable (n:W→Side)(H:∀ i,Even (n i).val)(x y:(i:W)→Site (n i))
variable [Fintype I](D:I→ RootEdge)(F: Libra.Keys G I→G.Color)
local notation "T!"=> WTax (d+2) d
-- uniform capped at m≥…
include hv hr
lemma Gift (a:W→ Bool)(e:RootEdge)(p q: W→ solar G d τ)(hF:r≤d)(hΘ:∀ i,m≤τ i)(v:ℝ)(hv':0≤v)(hG:ContDiffAt ℝ ω F 0)
    (H':∀ i,8≤ (n i).val) (ht:∀ i, Scent D e ≤ (n i).val) (he:∀ i,Variance.Cand r (F∘ dip D (n i) (x i))) (hq:∀ i,mind (p i).val (n i) (x i)=Cake (sett (n i) (x i) e) (a i) (Dune A) (Rh A) (F∘dip D _ (x i)) r) (hz:∀ i,Settle (x i) (y i) v): Permit n (WTax (d+2) d) (PortS n q m) fun i=> Warp A (H i) hp hs (x i) (y i) (p i) (q i) P :=by
       let L(i):=placed (n i) (x i) e; choose T hT using fun i=>PlotExcept (H i) (pathX (H i) (L i)) (H' i); let o(i):Stand.Free (T i):=⟨pathX (H i) (L i),hT i⟩; let E(i:W):=(edgesK (H i)).tick (L i); have ha(i:W): Plate (H i) (T i) (o i) (E i)=L i:= (resettle ..).symm
       let B i:= (a i).xor (dir (H i) (L i)); let Y(i):= F ∘dip D (n i) (x i); let V(i):=bredV A 0 (H i) hp hs; have hP:=PortPay (m:=m) n H T o y q A V B Y E he (fun i=>actsHere (x i) (H i) (o i) D F e (E i) (ha i) (ht i)) (fun i=>scentPaid D F n H T x i hG hF) (v*(1+ size e.1)) hΘ (by positivity) (fun i=>BeamF (x i) (y i) (H i) v (o i) e rfl (hz i) hv') hs hr hp hv; refine Eq.mpr ?_ hP; congr! 1
         -- cong
       funext j; dsimp only; rw [ha j,show (B j).xor (dir (H j) (L j))=a j from (by unfold B; simp only [Bool.xor_assoc,Bool.xor_self,Bool.xor_false]), ← show mind (p j).val (n j) (x j) = Cake (whiz (L j)) (a j) (Dune A) (Rh A) (Y j) r from hq j]; exact parade _ _ (V j) (p j) (q j) _ _ (T j) hr
end price
end YM.OPE.Variance
