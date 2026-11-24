import YM.Integration.WilsonAllDateHarvestHistoricalProgram
import YM.Integration.WilsonAllDateHarvestMovingProfile

/-! Submit the actual compact, separated rank-one constituents of the
measured smooth three-point test to the physical signed comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestNuclearProgram
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
local notation "CF" => R.family


open RG05Readout.Nuclear RG05Readout.Pulse

def Purchases (s:Fin 3→ℕ)(r η:ℝ)(w:(v:Fin 3)→(CF).label (s v)) {n m t N:ℕ}
    (nm:n ≤ m)(mt:m ≤ t)(tN:t ≤ N) (per d H k:ℕ) (P:(v:Fin 3)→Sight CF (s v) per)(fee:ℝ):Prop :=
  let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
  let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
  let y:=WilsonAllDateHarvestRebook.raised s S x m t
  let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
  ∀J:ℕ,∀o∈Pulse.area (C:=R.family) J,2*((CF).S.a n*(2*(J:ℝ)+1))<(CF).S.radius per →
    ∀roster:Census (Fin 3),∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) →
    Pulse.buy CF n per o (r*η/2) f →
    WilsonAllDateHarvestObservedReplay.Captured o (fun _=>(1,false)) s
      (fun z=>f z.val.1) R.makes P S y roster (nm.trans mt) tN (d+1) k (Q*((CF).S.a m/(CF).S.a t)) fee

include book in
theorem purchased (K:ℕ)(hk:5 ≤ K){η:ℝ}(hp:0<η):
    ∀ᶠr in trail,let m:=WilsonMeasuredWindow.stop (CF).path.levels simple K r
      ∀n:ℕ,∀nm:n ≤ m,∀t:ℕ,∀mt:m ≤ t,∀N:ℕ,∀tN:t ≤ N,∀per d H k:ℕ,
      ∀(s:Fin 3→ℕ)(w:(v:Fin 3)→(CF).label (s v))(P:(v:Fin 3)→Sight CF (s v) per)(fee:ℝ),
      Observed R portfolio L s r w nm mt tN per d H k P fee →
      Purchases R portfolio L s r η w nm mt tN per d H k P fee := by
  filter_upwards [WilsonAllDateHarvestClearance.original R simple hk hp] with r live m n nm t mt N tN per d H k s w P fee observed
  unfold Purchases
  intro S x y Q J o center margin roster f tall buy
  have weights (z:ManyStem CF o n):Cap (s z.val.1+2) (f z.val.1) 1:=by
    intro i hi u _
    simpa only [one_pow,one_mul] using tall z.val.1 i hi u
  have openAt:=live n per J nm o s f center margin buy roster
  exact WilsonAllDateHarvestHistoricalProgram.original book.tabs o (fun _=>(1,false)) s (fun z=>f z.val.1)
    R.makes P S x roster nm mt tN openAt
    (observed o (fun _=>(1,false)) (fun z=>f z.val.1) roster weights openAt)


include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:5 ≤ K){η:ℝ}(hp:0<η)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)
    (v:(i:Fin 3)→Free CF (s i)):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(CF).label (s i))(k:ℕ),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      ∀ᶠn:ℕ in atTop,∀ᶠr in trail,
      let m:=WilsonMeasuredWindow.stop (CF).path.levels simple K r
      let H:=2*(h+1)+2*(K+1)
      ∃nm:n ≤ m,∀charge:ℝ,1 ≤ charge → ∀ᶠt:ℕ in atTop,
      ∃mt:m ≤ t,n < t ∧ L.level r ≤ t+1 ∧ ∀per:ℕ,
        ∃P:(v:Fin 3)→Sight CF (s v) per,
          Registered R portfolio L s r (w r) n m (t+1) per d H P ∧
          Purchases R portfolio L s r η (w r) nm mt t.le_succ per d H k P charge⁻¹ := by
  obtain ⟨h,w,k,names,_,history⟩:=WilsonAllDateHarvestMovingProfile.original R simple W fund book portfolio slow
    L B E paid pegs near K d (by omega) s degree v
  refine ⟨h,w,k,names,?_⟩
  filter_upwards [history 1 zero_lt_one 0] with n deposited
  filter_upwards [deposited,purchased R simple book portfolio L K hk hp] with r course window
  intro m H
  obtain ⟨nm,receive⟩:=course
  refine ⟨nm,?_⟩
  intro charge one
  filter_upwards [receive charge one,eventually_gt_atTop n,eventually_ge_atTop (L.level r)] with t available nt high
  obtain ⟨mt,issue⟩:=available
  refine ⟨mt,nt,high.trans t.le_succ,?_⟩
  intro per
  obtain ⟨P,filed,observed⟩:=issue per
  refine ⟨P,filed,window n nm t mt (t+1) t.le_succ per d H k s (w r) P charge⁻¹ ?_⟩
  simpa only [pow_zero,mul_one,one_div] using observed

end YM.Integration.WilsonAllDateHarvestNuclearProgram

