import YM.Integration.WilsonReportHarvestSlabShiftCalendar
import YM.Integration.WilsonReportHarvestSlabShiftReceipt
import YM.Integration.WilsonSeparatedOriginalProfileCentral
import YM.Integration.WilsonAllDateHarvestNuclearProgram

/-! The original compact nuclear three-letter test and its fixed prescribed
frame have a genuine grade-zero representation of the physical difference
from the retained, signed old Wilson source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftSelected
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G : Gauge} (R : Run G) (simple : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (fund : FundedOriginalProperties.{u} simple δ W)
    (book : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (portfolio : Funding R) (slow : WilsonWindowReportingPace.Slow R.kit)

variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table} (L:Layout F)

variable {J:ℝ→FamilyBasis (C:=R.family) table} {u:Filter (ℕ×ℕ)}
    (B:Mantle F u) (E:OPE.Services R.family order table)
    (paid:Pier.Lair.Present F J) (pegs:Pegs B L)
    (near:∀ᶠ r in trail,R.family.S.a (L.level r) ≤ r ∧
      r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)


open WilsonAllDateHarvestFiledReplay
local notation "C" => R.family

open RG05Readout.Nuclear RG05Readout.Pulse Push.GridApprox

def Bought (K d h p D q b box:ℕ) (ε η:ℝ) (s:Fin 3→ℕ) (r:ℝ) (w:(v:Fin 3)→(C).label (s v))
    (nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r):Prop :=
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let n:=b+1
  let H:=2*(h+1)+2*(K+1)
  ∀charge:ℝ,1 ≤ charge → ∀ᶠ t:ℕ in atTop,∃mt:m ≤ t,∃nt:n < t,∀per:ℕ,
    let N:=t+1
    let g:=(Real.sqrt ((C).path.rep N per t).beta)⁻¹
    let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
    let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
    ∃P:(v:Fin 3)→Sight C (s v) per,Registered R portfolio L s r w n m N per d H P ∧
      ∀o∈Pulse.area («C»:=R.family) box,2*((C).S.a n*(2*(box:ℝ)+1)) < (C).S.radius per →
      ∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) → Pulse.buy C n per o (r*η/2) f →
        WilsonReportHarvestSlabShiftReceipt.Captured R nm mt nt t.le_succ s S P x o (fun _=>(1,false))
          (fun z=>f z.val.1) (ε*g^p/(charge*WilsonAllDateHarvestFixedSpectatorInvoice.extra R m t D q))

include W fund book slow B pegs near in
theorem chosen (K d box:ℕ)(hk:5 ≤ K){η:ℝ}(ep:0 < η)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)
    (v:(i:Fin 3)→Free C (s i))(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))
    (elected:∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r))
    (k:ℕ)(warm:∀ᶠn:ℕ in atTop,Warm C n (d+1) k):
    ∀ε:ℝ,0 < ε → ∀p D q:ℕ,∃b0:ℕ,∀ᶠr in trail,∀b≥b0,
      ∀nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r,
        Bought R simple portfolio L K d h p D q b box ε η s r (w r) nm := by
  intro ε hp p D q
  obtain ⟨kHigh,base,money⟩:=WilsonReportHarvestSlabShiftCalendar.chosen R simple W fund book portfolio slow L B pegs
    near K d (by omega) s degree v h w elected k warm ε hp p D q
  obtain ⟨root,central⟩:=eventually_atTop.mp (WilsonSeparatedOriginalProfileCentral.original R simple portfolio box)
  obtain ⟨stock,tiers⟩:=WilsonCloseCaptureFinances.original R simple W fund
  refine ⟨max base root,?_⟩
  filter_upwards [money,WilsonAllDateHarvestClearance.original R simple hk ep] with r current clear b late nm
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let n:=b+1
  let H:=2*(h+1)+2*(K+1)
  obtain ⟨stage,width,heated,paid⟩:=current b ((le_max_left ..).trans late) nm
  have place:=central b ((le_max_right ..).trans late)
  obtain ⟨F,one,spend⟩:=WilsonReportHarvestSlabReserve.original C simple b d
  unfold Bought
  intro m' n' H' charge fee
  have positive:1 ≤ F*charge:=one_le_mul_of_one_le_of_one_le one fee
  filter_upwards [paid (F*charge) positive] with t funds
  obtain ⟨mt,nt,bank⟩:=funds
  refine ⟨mt,nt,?_⟩
  intro per N g S x
  let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
  obtain ⟨P,δ,registered,pos,qone,margin,bought⟩:=bank per
  refine ⟨P,registered,?_⟩
  intro o center room f tall buy
  let E:Fin 3→Motion:=fun _=>(1,false)
  let heading:ManyStem C o n→Body:=fun z=>f z.val.1
  have occupied:Occupancy o ((C).path.levels.clock.J n):=fun cell=>(Finset.card_le_univ _).trans
    (by simpa only [Fintype.card_fin] using width)
  have cap (z:ManyStem C o n):Cap (s z.val.1+2) (heading z) 1:=by
    intro i hi u _
    simpa only [one_pow,one_mul] using tall z.val.1 i hi u
  have opened:=clear n per box nm o s f center room buy (Stock.census (Fin 3))
  have here:=place per o center
  have mesh:1 ≤ (C).S.a m/(C).S.a t:=(one_le_div ((C).S.a_pos t)).2 ((C).S.strictAnti.antitone mt)
  have qcash:1 ≤ Q*((C).S.a m/(C).S.a t):=one_le_mul_of_one_le_of_one_le qone mesh
  let extra:=WilsonAllDateHarvestFixedSpectatorInvoice.extra R m t D q
  have allot:ε*g^p/((F*charge)*extra)=(ε*g^p/(charge*extra))/F:=by ring
  have saved:=spend t nt k _ qcash δ (ε*g^p/(charge*extra)) pos.le (margin.trans_eq allot)
  exact WilsonReportHarvestSlabShiftReceipt.original R nm mt nt t.le_succ book stock tiers s S P x o E heading
    registered.1 occupied cap qone (fun v=>(registered.2 v).1) heated degree opened pos
    (bought o E heading (Stock.census (Fin 3)) cap) stage (here 0).1 (fun i=>(here i).2.2) saved

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:5 ≤ K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free C (s i)):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i)),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      ∀box:ℕ,∀η:ℝ,0 < η → ∀ε:ℝ,0 < ε → ∀p D q:ℕ,∃b0:ℕ,∀ᶠr in trail,∀b≥b0,
        ∀nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r,
          Bought R simple portfolio L K d h p D q b box ε η s r (w r) nm := by
  obtain ⟨h,w,elected,_⟩:=WilsonReportHarvestReplayPrescribed.original R simple W fund book portfolio slow L B E
    paid pegs near K d (by omega) s degree v
  obtain ⟨k,warm⟩:=(portfolio.dates 0 0 d 0).2
  exact ⟨h,w,elected,fun box _ ep=>chosen R simple W fund book portfolio slow L B pegs near K d box hk ep
    s degree v h w elected k warm⟩

end YM.Integration.WilsonReportHarvestSlabShiftSelected
