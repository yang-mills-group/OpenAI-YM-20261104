import YM.Integration.WilsonMacroscopicRichGradedCapture
import YM.Integration.WilsonMacroscopicRichEnrolledFiling
import YM.Integration.WilsonCloseCaptureFinances

/-! The upper rooted physical measurement and every earlier fixed filing share one original Wilson source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichGradedCalendar
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G) {b N per:ℕ}
set_option quotPrecheck false
local notation "C" => R.family
local notation "A" => (C).path
local notation "Y" => (C).path.rep N per
local notation "S" => (A).levels.clock.op b per
local notation "bill" => bling (A).levels b

open RG16.Literal
open Trace.Physical.GermGraph Extra.Histories.Relay

open WilsonLimitConstruction PhysicalNext
universe u

theorem original (simple:G.Simple){T:Campaign R}(W:Campaign.Pillars R T){δ:ℝ}
    (fund:FundedOriginalProperties.{u} simple δ W) (h m:ℕ) (start:(C).ref h ≤ m) (mb:m ≤ b)
    (top:b<N) (eligible:h+3 ≤ (A).levels.clock.J b) (η:ℝ) (ηpos:0<η)
    {o:Site ((C).side (b+1) per)} (home:(S).ratio.parent o=0)
    (X:Three G ((C).side (b+1) per)) (valid:Useful (Y (b+1)) X)
    {v:ℝ} (raw:MergeProof.Float.Blade (Y (b+1)) o X.2.1
      (profile (Y (b+1)).activities X.2.2) 0 v) (pos:0 ≤ v)
    (f:Cut C N per)(cont:Continuous f)(actual:X.1=credit C N per 0 f (b+1) top):
    let fee:=(C).S.a (b+1)^h*(bill*v)
    let E:=WilsonMacroscopicRichCaptureFilingBudget.capital C b fee η
    ∃ z:(C).label h, Next.UVStress.quota C h b N per z ≤ 2*E ∧
      ∀(i:ℕ),m ≤ i→∀(ib:i ≤ b)(door:Opened C h i per),
        Booked C N per h f i (ib.trans top.le) ∧
        mCost C h N per i (topReport C N per h R.makes i door (ib.trans top.le) f-
          ((C).factory h N per).terminal.symm z) ≤ E/gainChart A b i:=by
  have tiers:=(WilsonCloseCaptureFinances.original R simple W fund).2
  obtain ⟨⟨K,fmt,rem,size,source⟩,_⟩:=WilsonMacroscopicRichGradedCapture.original R h tiers top
    eligible home X valid raw pos f cont actual
  exact WilsonMacroscopicRichEnrolledFiling.original R.family N b m per h R.makes
    (R.again simple).1.scrim f cont K _ η ηpos start mb top.le fmt rem size source

end YM.Integration.WilsonMacroscopicRichGradedCalendar
