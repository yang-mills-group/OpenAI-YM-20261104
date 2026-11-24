import YM.Integration.WilsonAllDateHarvestRetainedCapture
import YM.Integration.WilsonReportHarvestReplayPrescribed

/-! Compare the genuine three submitted reporting labels with their lower
replayed history, using the very same cutoff columns and complete prior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFiledReplay
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u

variable {G:Gauge} (R:Run G) (portfolio:Funding R)
  {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
local notation "C" => R.family

def Registered (s:Fin 3→ℕ) (r:ℝ) (w:(v:Fin 3)→(C).label (s v))
    (n m N per d H:ℕ) (P:(v:Fin 3)→Sight C (s v) per):Prop :=
  let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
  let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
  let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
  (∀v,Spine R.doors portfolio.allowance R.makes n per (s v) N (P v) (S v)) ∧
    ∀v,size (x v) ≤ Q ∧ Many.point (S v) (x v) m N=chunk (WilsonReportingUnitOrbit.primary (s v))
      (((C).factory (s v) N per).terminal.symm (atRef L (s v) r (N,per) (w v)))

def Observed (s:Fin 3→ℕ) (r:ℝ) (w:(v:Fin 3)→(C).label (s v)) {n m t N:ℕ}
    (nm:n ≤ m) (mt:m ≤ t) (tN:t ≤ N) (per d H k:ℕ) (P:(v:Fin 3)→Sight C (s v) per) (fee:ℝ):Prop :=
  let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
  let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
  let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
  ∀(o:Fin 3→Site ((C).side n per))(E:Fin 3→Motion)(q:ManyStem C o n→Body)(roster:Census (Fin 3)),
    (∀v:ManyStem C o n,Cap (s v.val.1+2) (q v) 1) →
    Clearance o E s (headings o E q) roster m →
    WilsonAllDateHarvestHistoricalEntry.Captured o E s q R.makes P S x roster nm mt tN (d+1) k
      (Q*((C).S.a m/(C).S.a t)) fee

theorem original (simple:G.Simple)
    (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors)(stock:Storage C R.doors)
    (s:Fin 3→ℕ) (r:ℝ) (w:(v:Fin 3)→(C).label (s v)) {n m t N:ℕ}
    (nm:n ≤ m) (mt:m ≤ t) (nt:n < t) (tN:t ≤ N) (per d H kHigh k:ℕ)
    (P:(v:Fin 3)→Sight C (s v) per) (filed:Registered R portfolio L s r w n m N per d H P)
    (crowded:3 ≤ (C).path.levels.clock.J n) (warm:Warm C n (d+1) k)(degree:∀i,s i ≤ d)
    {δ fee:ℝ} (pos:0 < δ) (small:δ ≤ 1) (ep:0 < fee):
    let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
    let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
    let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
    1 ≤ Q → 2*δ*(WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) k (Q*((C).S.a m/(C).S.a t)))^3 ≤ fee →
    (∀(o:Fin 3→Site ((C).side n per))(E:Fin 3→Motion)(q:ManyStem C o n→Body)(roster:Census (Fin 3)),
     (∀v:ManyStem C o n,Cap (s v.val.1+2) (q v) 1) →
      WilsonReportHarvestReplayPhysical.Retained R nm mt tN s S P x o E q roster d kHigh Q δ) →
      Observed R portfolio L s r w nm mt tN per d H k P fee := by
  intro S Q x one budget tickets o E q roster cap clear
  have occupied:Occupancy o ((C).path.levels.clock.J n):=fun cell=>(Finset.card_le_univ _).trans
    (by simpa only [Fintype.card_fin] using crowded)
  have half:δ*(WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) k (Q*((C).S.a m/(C).S.a t)))^3 ≤ fee/2:=by
    linarith only [budget]
  exact WilsonAllDateHarvestRetainedCapture.original R simple nm mt nt tN book stock s S P x o E q roster
    filed.1 occupied cap one (fun v=>(filed.2 v).1) warm degree clear pos small ep half
    (tickets o E q roster cap)

end YM.Integration.WilsonAllDateHarvestFiledReplay
