import YM.Integration.WilsonAllDateHarvestFiledReplay
import YM.Integration.WilsonAllDateHarvestFixedOriginPhysical
import YM.Integration.WilsonAllDateHarvestFixedOriginInvoice

/-! Fix the coarse observation scale before reducing the separation. At each
fixed separation the cofinal original cutoff finances every older skin and
any prescribed finite period-independent inflation of the signed error. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFixedProfile
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

def Financed (K d h k p n:ℕ) (ε:ℝ) (s:Fin 3→ℕ) (r:ℝ)(w:(v:Fin 3)→(C).label (s v)):Prop :=
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let H:=2*(h+1)+2*(K+1)
  ∃nm:n ≤ m,∀charge:ℝ,1 ≤ charge → ∀ᶠt:ℕ in atTop,∃mt:m ≤ t,∀per:ℕ,
    let N:=t+1
    let g:=(Real.sqrt ((C).path.rep N per t).beta)⁻¹
    ∃P:(v:Fin 3)→Sight C (s v) per,Registered R portfolio L s r w n m N per d H P ∧
      Observed R portfolio L s r w nm mt t.le_succ per d H k P (ε*g^p/charge)

include W fund book slow B pegs near in
theorem chosen (K d:ℕ)(hk:0<K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free C (s i))
    (h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))
    (elected:∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r))
    (k:ℕ)(warm:∀ᶠn:ℕ in atTop,Warm C n (d+1) k):
    ∀ε:ℝ,0<ε → ∀p:ℕ,∀ᶠn:ℕ in atTop,∀ᶠr in trail,Financed R simple portfolio L K d h k p n ε s r (w r) := by
  obtain ⟨stock,_⟩:=WilsonCloseCaptureFinances.original R simple W fund
  intro ε ep p
  let H:=2*(h+1)+2*(K+1)
  let e:=WilsonAllDateHarvestFixedOriginInvoice.engineering d
  let l:=WilsonReportHarvestReplayIncome.reserve 0 d H k
  let η:=min ε 1
  have hp:0<η:=lt_min ep zero_lt_one
  have small:η/2 ≤ 1:=by have := min_le_right ε (1:ℝ); dsimp [η]; linarith
  obtain ⟨kHigh,paidUpper⟩:=WilsonAllDateHarvestFixedOriginPhysical.original R simple W fund book portfolio slow d
    (half_pos hp)
  have dates:=WilsonMeasuredWindow.stop_tendsto (C).path.levels simple K hk
  have balance:=WilsonReportHarvestReadmittedWallet.original R simple L K hk d h slow pegs.level.growing near
  filter_upwards [paidUpper p H e l,warm,(C).path.levels.fits.deep.eventually_ge_atTop 3] with n bought heated width
  filter_upwards [elected,balance,dates.eventually_ge_atTop n,
    dates.eventually (WilsonAllDateHarvestFixedOriginInvoice.original R simple d H k p hp),
    dates.eventually (WilsonAllDateHarvestFixedOriginInvoice.amount_le R simple (half_pos hp) small)]
    with r names funded nm money collar
  unfold Financed
  intro m H'
  refine ⟨nm,?_⟩
  intro charge one
  filter_upwards [money n nm charge one,eventually_ge_atTop (L.level r)] with t window rid
  obtain ⟨mt,mature,nt,rent⟩:=window
  refine ⟨mt,?_⟩
  intro per N g
  let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
  let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w r v) (S v) m N per
  obtain ⟨P,spine,upper⟩:=bought m nm t mt mature per s degree
  have booked:Registered R portfolio L s r (w r) n m N per d H P:=
    ⟨spine,fun v=>funded n (s v) N per nm (max_le (rid.trans t.le_succ) (mt.trans t.le_succ)) (degree v)
      R.doors portfolio.allowance (P v) (S v) (spine v) (w r v) (names v).2⟩
  obtain ⟨gp,_,pos,usable⟩:=collar t mt N t.le_succ per n p e l
  have cp:0 < charge:=zero_lt_one.trans_le one
  have target:η*g^p/charge ≤ ε*g^p/charge:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg gp.le _)) cp.le
  refine ⟨P,booked,WilsonAllDateHarvestFiledReplay.original R portfolio L simple book stock s r (w r)
    nm mt nt t.le_succ per d H kHigh k P booked width heated degree pos usable (div_pos (mul_pos ep (pow_pos gp _)) cp)
    (rent per).1 ((rent per).2.trans target) ?_⟩
  exact upper x (fun v=>(booked.2 v).1)

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:0<K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free C (s i)):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))(k:ℕ),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      ∀ε:ℝ,0<ε → ∀p:ℕ,∀ᶠn:ℕ in atTop,∀ᶠr in trail,Financed R simple portfolio L K d h k p n ε s r (w r) := by
  obtain ⟨h,w,elected,_⟩:=WilsonReportHarvestReplayPrescribed.original R simple W fund book portfolio slow L B E
    paid pegs near K d hk s degree v
  obtain ⟨k,warm⟩:=(portfolio.dates 0 0 d 0).2
  exact ⟨h,w,k,elected,chosen R simple W fund book portfolio slow L B pegs near K d hk s degree v h w elected k warm⟩

end YM.Integration.WilsonAllDateHarvestFixedProfile
