import YM.Integration.WilsonOriginalFullRosterPhysicalMoney

/-! The genuine dated return and its verified financial filing on the same two chronological prints. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterEarnedBill
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "actors" => WilsonOriginalMixedBlockRows.room V
local notation "nulls" => fun _:V => (⊥:Submodule ℝ ℂ)
variable {S S': V → ℝ}{a a':ℕ}
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census V))
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1)))
local notation "high" => upper.post
local notation "low" => lower.post
local notation "vac" => Ψ (j+1)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead (actors) (high).model upper.order (high).voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le base) (high).lesson
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
local notation "home" => ((high).passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "gc" => Coat.gStep (vac).beta
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "nh" => ((∑v:V,upper.grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,lower.grades v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
local notation "rank" => max ((∑v:V,upper.grades v)+1) ((∑v:V,lower.grades v)+1)

open WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
local notation "gf" => Coat.gStep (Ψ (j+1+1)).beta
local notation "carried" => Mutation.grow (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
  (gf) (gc) (vac) (high).output
local notation "fig" => Oak.figureReal R hk D Q π Γ books (Nat.le_succ_of_le base) (high).op (high).lesson ahead upper.order upper.shelf
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead upper.order upper.shelf
local notation "w₂" => Stoop.radius (high).w ((Ω)^6)


theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (read:WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower s charges q h target ε δ C)
    (budget:2 ≤ C)(small:regulatorRun R.family N per (j+1) ≤ 1)
    (cooled:(1+ε)*(regulatorRun R.family N per (j+1+1))^q ≤ 1)
    (p:ℕ)(tol:ℝ){i:ℕ}(older:i ≤ j+1)(U:Config G (R.family.side i per))
    (earned:WilsonOriginalFullRosterFiledHearing.Earned R simple hk D Q π Γ Ψ books base ahead rows upper lower
      course live way pass month hospital read p tol older U):
    let g:=regulatorRun R.family N per (j+1)
    (carried).hard=(high).output.hard ∧ ((upper.appointment.row upper.x).A.density (upper.appointment.row upper.x).x=
      LocalComparison.actualPush R.family N per (j+1) (rows (j+1+1))) ∧
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (upper.appointment.row upper.x) (lower.law lower.x) s,
      F.α=(vac).p.supportExponent+1+1 ∧ F.h=h ∧ F.δ=δ ∧ F.W ≤ C*H^(fee charges s) ∧
      F.gross ≤ C*H^2*(g⁻¹)^(rank) ∧ F.M ≤ C*H^(fee charges s+2)*(g⁻¹)^(rank) ∧
      F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q ∧
      ‖WilsonOriginalJointTrialHearing.fee R N per U rows (j+1) s-
        WilsonOriginalOccupiedWindow.credit R (marks) (N:=N) older Ψ (upper.appointment.row upper.x) s U‖ ≤
      F.bill i tol H (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per) (R.family.path.β N per (i+1)) U) p:=by
  obtain ⟨F,account,wallet,gross,total,rent⟩:=WilsonOriginalFullRosterPhysicalMoney.original R simple hk D Q π Γ Ψ
    books base ahead rows upper lower course live way pass month hospital warm nn nn' read budget small cooled
  obtain ⟨fw,fr,fg,committed,width,shape,accuracy⟩:=account
  obtain ⟨hard,joint,heard⟩:=earned
  refine ⟨hard,joint,F,width,shape,accuracy,wallet,gross,total,rent,?_⟩
  unfold WilsonOriginalMountedRegular.Filing.bill
  rw [fw,fr,fg,committed,width,shape,accuracy]
  exact heard

end YM.Integration.WilsonOriginalFullRosterEarnedBill
end
