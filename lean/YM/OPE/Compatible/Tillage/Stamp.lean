import YM.OPE.Compatible.Tillage.Pier
/-! # Shape added charges -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
variable {V:ChartRatio G}{p q:Clip}{R T:PathData G}
lemma vote_eq (P:Patch)(K:KernelChoices)(R:PathData G)(p:Clip) (n:ℕ): voteV P K R p n=payVolume (drip G P.L) (inkV R p n)+expose (stationCall P K G n):=by
   unfold inkV voteV Penna expose podium; rw [volVShape,smul_add]
namespace Boxes
variable (X: Boxes G P K)
def Tell (k:ℕ):= stitch (raft X.main (expose (stationCall P K G k)))
def Exc (R:PathData G)(p:Clip):=stitch (raft X.main ((-3:ℝ) • X.Fly R p))
def Hort (R:PathData G)(p:Clip)(V:ChartRatio G):=stitch (raft X.main (X.lip R p + (-1:ℝ) • collarH P V))
lemma pole_t (n:ℕ) (h:R.Bounds p σ u C) : stitch (raft X.main (voteV P K R p n))=stitch (player X (inkV R p n))+X.Tell n :=by
    have hx:=folk_volP (drip_cash G P.L) (p:=inkV R p n) (fun i=> (inkSongs _ _ 1 n i h).2.1); have hc:folk (expose (stationCall P K G n)):= folkS (fun m=>callCost P K G n m) _; rw [vote_eq,raftPlus _ X.rocket2 hx hc,stitchAdd (folkT X.rocket2 hx) (folkT X.rocket2 hc)]; rfl
lemma T3split (h:R.Bounds p σ u C):stitch (X.T3 R p)=stitch (player X (inkV R p 3))+X.Tell 3:= X.pole_t 3 h
lemma T4split (h:R.Bounds p σ u C): stitch (X.T4 R p) = stitch (player X (inkV R p 4))+X.Tell 4+X.Exc R p:=by
    have hh:= folkS (X.folk_fly h) (-3:ℝ); have ht:= folkS (penne_unit R p P K h 4) ((Nat.factorial 4):ℝ); unfold T4 Om; rw [raftPlus _ X.rocket2 ht hh,stitchAdd (folkT X.rocket2 ht) (folkT X.rocket2 hh),X.pole_t 4 h]; rfl
lemma T2split (h:R.Bounds p σ u C) (V:ChartRatio G): stitch (X.talo R p V)=stitch (player X (leafV R 2))+X.Hort R p V :=by
    have hh:= folkF (X.folk_lip h) (folkS (folk_cap P V) (-1:ℝ)); have hp:=folk_collar P h; unfold talo crownZ; rw [add_assoc,raftPlus _ X.rocket2 hp hh,stitchAdd (folkT X.rocket2 hp) (folkT X.rocket2 hh)]; rfl
end Boxes
end Script
end YM.OPE.Flume
