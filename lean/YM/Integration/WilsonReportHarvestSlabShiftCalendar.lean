import YM.Integration.WilsonAllDateHarvestFixedSpectatorInvoice
import YM.Integration.WilsonAllDateHarvestFixedProfile
import YM.Integration.WilsonReportHarvestSlabReserve

/-! Finance the signed capture for the very same preselected physical
columns. The threshold for the older origin precedes the physical
separation, so both fixed and moving capture dates are admitted. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftCalendar
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

def Financed (K d h k kHigh p D q b:ℕ) (ε:ℝ) (s:Fin 3→ℕ) (r:ℝ)(w:(v:Fin 3)→(C).label (s v))
    (nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r):Prop :=
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let n:=b+1
  let H:=2*(h+1)+2*(K+1)
  3 ≤ (C).path.levels.clock.J b ∧ 3 ≤ (C).path.levels.clock.J n ∧ Warm C n (d+1) k ∧
  ∀charge:ℝ,1 ≤ charge → ∀ᶠ t:ℕ in atTop,∃mt:m ≤ t,n < t ∧ ∀per:ℕ,
    let N:=t+1
    let g:=(Real.sqrt ((C).path.rep N per t).beta)⁻¹
    let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
    let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
    let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
    ∃ (P:(v:Fin 3)→Sight C (s v) per) (δ:ℝ),Registered R portfolio L s r w n m N per d H P ∧
      0<δ ∧ 1 ≤ Q ∧
      2*δ*(WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) k (Q*((C).S.a m/(C).S.a t)))^3 ≤ ε*g^p/(charge*WilsonAllDateHarvestFixedSpectatorInvoice.extra R m t D q) ∧
      ∀ (o:Fin 3→Site ((C).side n per)) (E:Fin 3→Motion) (q:ManyStem C o n→Body) (roster:Census (Fin 3)),
        (∀v:ManyStem C o n,Cap (s v.val.1+2) (q v) 1) →
        WilsonReportHarvestReplayPhysical.Retained R nm mt t.le_succ s S P x o E q roster d kHigh Q δ

include W fund book slow B pegs near in
theorem chosen (K d:ℕ)(hk:0 < K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free C (s i))
    (h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))
    (elected:∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r))
    (k:ℕ)(warm:∀ᶠn:ℕ in atTop,Warm C n (d+1) k):
    ∀ε:ℝ,0<ε → ∀p D q:ℕ,∃ kHigh b0:ℕ,∀ᶠr in trail,∀b≥b0,
      ∀nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r,
        Financed R simple portfolio L K d h k kHigh p D q b ε s r (w r) nm := by
  intro ε ep p D q
  let H:=2*(h+1)+2*(K+1)
  let e:=WilsonAllDateHarvestFixedSpectatorInvoice.engineering d D
  let l:=WilsonReportHarvestReplayIncome.reserve 0 d H k
  let η:=min ε 1
  have hp:0<η:=lt_min ep zero_lt_one
  have small:η/2 ≤ 1:=(half_le_self hp.le).trans (min_le_right _ _)
  obtain ⟨kHigh,paidUpper⟩:=WilsonAllDateHarvestFixedOriginPhysical.original R simple W fund book portfolio slow d
    (half_pos hp)
  have dates:=WilsonMeasuredWindow.stop_tendsto (C).path.levels simple K hk
  have balance:=WilsonReportHarvestReadmittedWallet.original R simple L K hk d h slow pegs.level.growing near
  obtain ⟨i0,issued⟩:=eventually_atTop.mp ((paidUpper p H e l).and (warm.and ((C).path.levels.fits.deep.eventually_ge_atTop 3)))
  refine ⟨kHigh,i0,?_⟩
  filter_upwards [elected,balance,dates.eventually (WilsonAllDateHarvestFixedSpectatorInvoice.original R simple slow.2 d H k p D q hp),
    dates.eventually (WilsonAllDateHarvestFixedOriginInvoice.amount_le R simple (half_pos hp) small)]
    with r names funded money collar b late nm
  have next:=issued (b+1) (late.trans b.le_succ)
  have stage:3 ≤ (C).path.levels.clock.J b:=(issued b late).2.2
  rcases next with ⟨bought,heated,width⟩
  unfold Financed
  intro m n H'
  refine ⟨stage,width,heated,fun charge one=>?_⟩
  filter_upwards [money n nm charge one,eventually_ge_atTop (L.level r)] with t window rid
  obtain ⟨mt,mature,nt,rent⟩:=window
  refine ⟨mt,nt,?_⟩
  intro per N g S Q x
  obtain ⟨P,spine,upper⟩:=bought m nm t mt mature per s degree
  have booked:Registered R portfolio L s r (w r) n m N per d H P:=
    ⟨spine,fun v=>funded n (s v) N per nm (max_le (rid.trans t.le_succ) (mt.trans t.le_succ)) (degree v)
      R.doors portfolio.allowance (P v) (S v) (spine v) (w r v) (names v).2⟩
  obtain ⟨gp,_,pos,_⟩:=collar t mt N t.le_succ per n p e l
  let z:=WilsonAllDateHarvestFixedSpectatorInvoice.extra R m t D q
  have target:η*g^p/(charge*z) ≤ ε*g^p/(charge*z):=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg gp.le _)) (mul_nonneg (zero_le_one.trans one) (rent per).2.1.le)
  refine ⟨P,_,booked,pos,(rent per).1,(rent per).2.2.trans target,?_⟩
  exact upper x (fun v=>(booked.2 v).1)

end YM.Integration.WilsonReportHarvestSlabShiftCalendar
