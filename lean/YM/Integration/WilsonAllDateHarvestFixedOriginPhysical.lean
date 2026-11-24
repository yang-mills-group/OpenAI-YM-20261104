import YM.Integration.WilsonAllDateHarvestFixedOriginEntries
import YM.Integration.WilsonReportHarvestReplayPhysical

/-! Original finite Wilson source at the last available ultraviolet step.
The physical catalogue is still based at its independently fixed earlier
scale, including when the measured reporting date lies arbitrarily later. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFixedOriginPhysical
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open RG12
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G : Gauge} (R : Run G) (simple : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (fund : FundedOriginalProperties.{u} simple δ W)
    (book : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (portfolio : Funding R) (slow : WilsonWindowReportingPace.Slow R.kit)

open WilsonReportHarvestReplayPhysical
local notation "C" => R.family

include W fund book slow in
theorem original (d:ℕ){ε:ℝ}(ep:0<ε):
    ∃k:ℕ,∀p h engineering reserve:ℕ,∀ᶠ b:ℕ in atTop,∀m:ℕ,∀bm:b ≤ m,
      ∀j:ℕ,∀mj:m ≤ j,m-b ≤ j-m→∀per:ℕ,∀s:Fin 3→ℕ,(∀v,s v ≤ d) →
      let N:=j+1
      let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
      let Q:=allowance R m N d h
      ∃P:(v:Fin 3)→Sight C (s v) per,
        (∀v,Spine R.doors portfolio.allowance R.makes b per (s v) N (P v) (S v)) ∧
        ∀(x:(v:Fin 3)→Palette C (s v)),(∀v,size (x v) ≤ Q) →
        ∀(o:Fin 3→Site ((C).side b per))(E:Fin 3→Motion)(q:ManyStem C o b→Body)(roster:Census (Fin 3)),
        (∀v:ManyStem C o b,Cap (s v.val.1+2) (q v) 1) →
          WilsonReportHarvestReplayPhysical.Retained R bm mj j.le_succ s S P x o E q roster d k Q (amount R b m j N per p engineering reserve ε) := by
  obtain ⟨k,fundDates⟩:=WilsonAllDateHarvestFunding.original R simple W fund book portfolio slow d ep
  refine ⟨k,?_⟩
  intro p h engineering reserve
  obtain ⟨start,terms⟩:=eventually_atTop.mp (WilsonAllDateHarvestFixedOriginEntries.original R simple p k h engineering
    (2*(d+2)) (2*(d+2)) reserve ep)
  obtain ⟨age,upper⟩:=eventually_atTop.mp (WilsonReportHarvestUpperRange.original R simple d h)
  filter_upwards [fundDates,eventually_ge_atTop start,eventually_ge_atTop age] with b booked sb ab
  intro m bm j mj mature per s degree N S Q
  have mN:m ≤ N:=mj.trans j.le_succ
  obtain ⟨P,spine,grant⟩:=booked m bm N mN per s degree
  refine ⟨P,spine,?_⟩
  intro x sizes o E q roster cap
  have live:j<N:=Nat.lt_succ_self j
  obtain ⟨one,ceiling,_⟩:=upper m (ab.trans bm) j mj j mj le_rfl (WilsonReportHarvestUpperRange.latest _ mj)
  have qp:0<Q:=mul_pos (pow_pos (zero_lt_one.trans ((C).path.levels.fits.delayed m)) h) (zero_lt_one.trans_le one)
  obtain ⟨integral,board,mixed,_⟩:=grant o E q x roster (fun _=>Q) cap sizes (fun _=>qp) j mj live.le
  unfold WilsonReportHarvestReplayPhysical.Retained
  dsimp only
  refine ⟨integral,?_,fun U=>board.check (R.makes.wilson.represents N per j live.le).good.labels U,mixed,?_⟩
  · simpa only [if_neg live.ne] using board
  · exact terms m (sb.trans bm) j mj N live per (d+1) b bm mature o E roster (fun _=>Q) _ _
      (WilsonReportHarvestUpperRange.factor (C).S d m N) one ceiling (fun _=>qp) (fun _=>le_rfl)
      (by simpa only [if_neg live.ne] using board)

end YM.Integration.WilsonAllDateHarvestFixedOriginPhysical
