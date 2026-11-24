import YM.Integration.WilsonAllDateHarvestFixedProfile
import YM.Integration.WilsonReportHarvestReplayIncome

/-! The same three prescribed reporting labels are used in every comparison:
both measured origins for every eligible upper board, and the independently
fixed physical observation lattice before the separation tends to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestMovingProfile
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

def Financed (K d h k p:ℕ)(ε:ℝ)(s:Fin 3→ℕ)(r:ℝ)(w:(v:Fin 3)→(C).label (s v)):Prop :=
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let b:=crossLevel (C).S r-1-1
  let H:=2*(h+1)+2*(K+1)
  ∀n:ℕ,b ≤ n → n ≤ b+1 → ∃nm:n ≤ m,∀u≥m,L.level r ≤ u+1 → ∀per:ℕ,
    let N:=u+1
    ∃P:(v:Fin 3)→Sight C (s v) per,Registered R portfolio L s r w n m N per d H P ∧
      ∀t:ℕ,∀mt:m ≤ t,∀tu:t ≤ u,WilsonReportHarvestUpperRange.eligible (C).S m t u →
      let g:=(Real.sqrt ((C).path.rep N per t).beta)⁻¹
      Observed R portfolio L s r w nm mt (Nat.le_succ_of_le tu) per d H k P (ε*g^p)

include W fund book slow in
theorem moving (K d:ℕ)(hk:0<K)(s:Fin 3→ℕ)(degree:∀v,s v ≤ d)
    (h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))(k:ℕ)(warm:∀ᶠn:ℕ in atTop,Warm C n (d+1) k)
    (issued:∀a:ℝ,0<a → ∃kHigh:ℕ,∀p e l:ℕ,∀ᶠr in trail,
      WilsonReportHarvestReplayPrescribed.Received R simple portfolio L K d h kHigh p e l a s r (w r)):
    ∀ε:ℝ,0<ε → ∀p:ℕ,∀ᶠr in trail,Financed R simple portfolio L K d h k p ε s r (w r) := by
  obtain ⟨stock,_⟩:=WilsonCloseCaptureFinances.original R simple W fund
  obtain ⟨start,ready⟩:=eventually_atTop.mp (warm.and ((C).path.levels.fits.deep.eventually_ge_atTop 3))
  intro ε ep p
  let H:=2*(h+1)+2*(K+1)
  let e:=WilsonReportHarvestReplayIncome.engineering d
  let l:=WilsonReportHarvestReplayIncome.reserve K d H k
  let η:=min ε 1
  have hp:0<η:=lt_min ep zero_lt_one
  have small:η/2 ≤ 1:=by have := min_le_right ε (1:ℝ); dsimp [η]; linarith
  obtain ⟨kHigh,source⟩:=issued (η/2) (half_pos hp)
  have dates:=WilsonMeasuredWindow.stop_tendsto (C).path.levels simple K hk
  have range:=(WilsonMixedTaggedMeasuredWindow.original R simple K hk slow.2).2
  filter_upwards [source p e l,WilsonReportHarvestReplayIncome.original R simple K hk d H k p hp slow,
    dates.eventually (WilsonAllDateHarvestFixedOriginInvoice.amount_le R simple (half_pos hp) small),range,
    (WilsonMixedTaggedSpend.lower R).eventually_ge_atTop start] with r tickets income collar window late
  unfold Financed
  intro m b H' n bn nb
  obtain ⟨nm,issuedAt⟩:=tickets n bn nb
  refine ⟨nm,?_⟩
  intro u mu cut per N
  obtain ⟨P,basis,size,sourceAt⟩:=issuedAt u mu cut per
  have booked:Registered R portfolio L s r (w r) n m N per d H P:=⟨basis,size⟩
  refine ⟨P,booked,?_⟩
  intro t mt tu eligible g
  have ht:t ≤ N:=Nat.le_succ_of_le tu
  have readyAt:=ready n (late.trans bn)
  have nm' : n < m := nb.trans_lt window.1
  have geo:1 ≤ (C).S.a m/(C).S.a N:=(one_le_div ((C).S.a_pos N)).2
    ((C).S.strictAnti.antitone (mu.trans u.le_succ))
  have one:1 ≤ WilsonReportHarvestReplayPhysical.allowance R m N d H:=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ ((C).path.levels.fits.delayed m).le) (one_le_pow₀ geo)
  obtain ⟨gp,_,pos,usable⟩:=collar t mt N ht per n p e l
  have target:η*g^p ≤ ε*g^p:=mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg gp.le _)
  exact WilsonAllDateHarvestFiledReplay.original R portfolio L simple book stock s r (w r) nm mt (nm'.trans_le mt)
    ht per d H kHigh k P booked readyAt.2 readyAt.1 degree pos usable (mul_pos ep (pow_pos gp _)) one
    ((income n bn nb u mu t mt tu eligible per).2.trans target)
    (fun o E q roster cap=>sourceAt o E q roster cap t mt tu eligible)

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:0<K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free C (s i)):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))(k:ℕ),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      (∀ε:ℝ,0<ε → ∀p:ℕ,∀ᶠr in trail,Financed R simple portfolio L K d h k p ε s r (w r)) ∧
      ∀ε:ℝ,0<ε → ∀p:ℕ,∀ᶠn:ℕ in atTop,∀ᶠr in trail,
        WilsonAllDateHarvestFixedProfile.Financed R simple portfolio L K d h k p n ε s r (w r) := by
  obtain ⟨h,w,elected,issued⟩:=WilsonReportHarvestReplayPrescribed.original R simple W fund book portfolio slow L B E
    paid pegs near K d hk s degree v
  obtain ⟨k,warm⟩:=(portfolio.dates 0 0 d 0).2
  exact ⟨h,w,k,elected,moving R simple W fund book portfolio slow L K d hk s degree h w k warm issued,
    WilsonAllDateHarvestFixedProfile.chosen R simple W fund book portfolio slow L B pegs near K d hk s degree v h w elected k warm⟩

end YM.Integration.WilsonAllDateHarvestMovingProfile
