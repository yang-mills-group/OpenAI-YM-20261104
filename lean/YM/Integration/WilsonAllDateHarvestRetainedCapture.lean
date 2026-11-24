import YM.Integration.WilsonAllDateHarvestHistoricalEntry
import YM.Integration.WilsonReportHarvestReplayPhysical

/-! Spend the complete signed physical upper reporting receipt on the real
earlier history. The independent lower warm radius may be chosen after its
own genuine enrollment and before any cutoff or observation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestRetainedCapture
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open RG12
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family

include simple in
theorem original {n a t N per d kHigh kLow:ℕ} (na:n ≤ a) (aturn:a ≤ t) (nt:n < t) (tN:t ≤ N)
    (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors) (stock:Storage C R.doors)
    {B:ℕ→ℕ→ℝ} (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side n per))(E:Fin 3→Motion)
    (q:ManyStem C o n→Body)(roster:Census (Fin 3))
    (basis:∀i,Spine R.doors B R.makes n per (s i) N (P i) (S i))
    (occ:Occupancy o ((C).path.levels.clock.J n))
    (cap:∀i:ManyStem C o n,Cap (s i.val.1+2) (q i) 1)
    {Q δ fee:ℝ} (one:1 ≤ Q) (size:∀i,size (x i) ≤ Q)
    (warm:Warm C n (d+1) kLow) (degree:∀i,s i ≤ d)
    (clear:Clearance o E s (headings o E q) roster a)
    (pos:0 < δ) (small:δ ≤ 1) (ep:0 < fee)
    (budget:δ*(WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) kLow
      (Q*((C).S.a a/(C).S.a t)))^3 ≤ fee/2)
    (retained:WilsonReportHarvestReplayPhysical.Retained R na aturn tN s S P x o E q roster d kHigh Q δ) :
    WilsonAllDateHarvestHistoricalEntry.Captured o E s q R.makes P S x roster na aturn tN
      (d+1) kLow (Q*((C).S.a a/(C).S.a t)) fee := by
  cases t with
  | zero => omega
  | succ t =>
    obtain ⟨_,board,_,_,H,K,legal,issued,regular,hard⟩:=retained
    exact WilsonAllDateHarvestHistoricalEntry.original o E s q R.makes book stock P S x roster simple basis
      (Nat.le_of_lt_succ nt) na aturn tN occ cap one size warm degree clear board.fettled
      pos small ep budget H K legal issued regular hard

end YM.Integration.WilsonAllDateHarvestRetainedCapture
