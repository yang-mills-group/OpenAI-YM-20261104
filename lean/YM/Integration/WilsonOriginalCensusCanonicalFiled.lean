import YM.Integration.WilsonOriginalCensusCanonicalPost
import YM.Integration.WilsonOriginalDatedCensusInput
import YM.Integration.WilsonOriginalDepositedModelBook

/-! The canonical cutoff post sold on its own nonbare vacuum, with its actual occupied register and inverse wallet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalFiled
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  {V:Type}[Fintype V][DecidableEq V](d:V→ℕ)(q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  (o:V→Site (R.family.side (i+1) per))(order shelf:ℕ)

local notation "H" => Ψ (i+1)
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M" => row R d q hd o scale
local notation "A" => room V
local notation "K₀" => (fun _:V=>(⊥:Submodule ℝ ℂ))
local notation "marks" => Stock.census V
local notation "w₀" => (fun _:V=>(1:ℝ))
local notation "C₀" => charge R d q scale w₀
local notation "g" => Coat.gStep (H).beta
local notation "D₀" => (∑v:V,d v)+1
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "physical" => fun (x:Wallet (A))(U:Config G (R.family.side (i+1) per))=>
  ((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) x U)
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀)
  d order shelf op.count i hi (physical)

local notation "S₀" => (fun _:V=>max 1 (C₀))
local notation "e₀" => ((D₀)+5)*Fintype.card V
local notation "rate" => fun s:(marks).Mode=>(R.alloy.B.a.clock.hatBeta i)^(e₀)*Poly.toll (S₀) s
local notation "pupil" F:max => Oak.student (n:=per) R hk D Q π Γ books hi (F).op (F).lesson
  ahead (A) (F).model order (F).voter

private theorem uncut_at {V I J₀ X:Type}[DecidableEq V]{Γ₀:Marker.Census V}{n:Side}{G:Gauge}
    {p₀ p₁:Earn.Passport n V}{M₀:I→Earn.Row p₀ Γ₀ G X}{M₁:J₀→Earn.Row p₁ Γ₀ G X}
    (home:p₀=p₁)(names:I=J₀)(same:HEq M₀ M₁)(b:BudgetPoint)(y:ℝ)(x:X)(U:Config G n):
    WilsonRootedKioskOccupiedSlip.bare (rendered M₀ b y) x U = Spill.Foundry.uncut M₁ y x U:=by
  subst p₁ J₀
  rw [eq_of_heq same]
  rfl

include simple course cut hospital in
/-- Sell the post already selected on this original course, at all wallets. -/
theorem booked (F:Ptype)(home:F.passport=Passport.point o)(names:F.modelIndex=V)(same:HEq F.model (M))
    (event:F.op=op)(income:∀v,(F.w v)⁻¹≤(S₀) v*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2)))
    (count:op.count ≤ Burn.horizon k+2)(level:shelf ≤ R.alloy.B.a.clock.J i)
    (pass:Pass D Q R.alloy R.kit)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i)
    (p:ℕ)(way:WayStation R.kit)(hardFloor:6*op.count ≤ R.alloy.B.a.clock.J i)
    (deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged (by norm_num:0<(1:ℝ)) ≤ i)
    (more:WilsonMeasuredSemesterSubpower.onset R op.count (by norm_num:0<(1:ℝ)) ≤ i)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ i+1)
    (fresh:(eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple
      (Fintype.card V) (order+shelf+1+(D₀)) ((D₀)+2))).choose ≤ i):
    Nonempty (WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (A) (K₀)
      d order shelf op.count (physical) F (rate)):=by
  have declaration (x:Wallet (A))(U:Config G (R.family.side (i+1) per)) :
      (physical) x U=((H).eval U:ℂ) • Poly.pass
        (WilsonRootedKioskOccupiedSlip.bare (rendered F.model (H).p (g)) x U):=by
    rw [uncut_at home names same (H).p (g) x U]
  have paidRows (t:Wallet (A)) : ∃row:WilsonOriginalOccupiedWindow.Slice R (marks) (Ψ i),
      row.w=F.w ∧ row.hard=1 ∧ WilsonOriginalOccupiedSalary.debit row.regular row.hard ≤ 10*χ ∧
      (∀s:(marks).Mode,(WilsonOriginalOccupiedSalary.debit row.regular row.hard)^s.val.card ≤
        (R.alloy.B.a.clock.hatBeta i)^(e₀)*(Poly.toll (S₀) s*Poly.toll row.w s)) ∧
      row.A.density row.x=LocalComparison.actualPush R.family N per i ((physical) t) ∧
      row.A.E.log row.x=((rendered (pupil F) (Ψ i).p (g)).join F.output.old).log t:=by
    have co:F.op.count=op.count:=congrArg _ event
    have funded:∀s:(marks).Mode,(∑v∈s.val,d v)+1 ≤ (D₀):=fun _=>Nat.succ_le_succ
      (sum_le_sum_of_subset_of_nonneg (f:=d) (subset_univ _) (fun _ _ _=>Nat.zero_le _))
    obtain ⟨row,ww,reg,hr,whole,lamps,_⟩:=WilsonOriginalOccupiedFiledSlice.original R hk D Q π Γ Ψ
      books hi cut ahead (A) (K₀) d order shelf op.count (physical) F simple way course (D₀) p funded
      hardFloor deep aged (by norm_num:0<(1:ℝ)) (by simpa only [co] using opened) t
    have cold:=(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec (i+1)
      cooled N per cut
    have small:Pert.Asymptotics.regulatorRun R.family N per (i+1) ≤ 1:=by linarith only [cold.1,cold.2]
    have served:=WilsonOriginalOccupiedFiledFare.original R hk D Q π Γ Ψ course books hi cut ahead
      (A) (K₀) d order shelf op.count (physical) F pass hospital level (by simpa only [co] using count)
      onset (by simpa only [co] using more) F.small p 1 (by
        rw [one_mul]; change (Pert.Asymptotics.regulatorRun R.family N per (i+1))^p ≤ 1
        exact pow_le_one₀ cold.1.le small)
    have debit:WilsonOriginalOccupiedSalary.debit row.regular row.hard ≤ 10*χ:=by simpa only [reg,hr] using served
    obtain ⟨_,_,_,_,joint⟩:=WilsonOriginalFreshJoinedRows.earned R hk D Q π Γ Ψ books hi cut ahead
      (A) (K₀) d order shelf op.count (physical) F simple way course (D₀) p funded hardFloor deep aged
      (by norm_num:0<(1:ℝ)) (by simpa only [co] using opened) t
    refine ⟨row,ww,hr,debit,?_,whole,funext fun U=>(lamps U).trans (joint U).symm⟩
    intro s
    apply (eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple (Fintype.card V)
      (order+shelf+1+(D₀)) ((D₀)+2))).choose_spec i fresh s (Finset.card_le_univ s.val) row.w
      row.positive (S₀) (zero_le_one.trans (le_max_left ..)) debit
      (fun _=>zero_lt_one.trans_le (le_max_left ..))
    simpa only [ww] using income

  choose row radius resident height fare received joined using paidRows
  exact ⟨{ declared:=declaration, row:=row, radius:=radius, resident:=resident, height:=height,
           wage:=fun t s=>(fare t s).trans_eq (mul_assoc ..).symm,
           density:=received, mounted:=joined }⟩

/-- Each fixed wallet files the full original source on exactly this post and appointment. -/
def file (F:Ptype)(book:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead
    (A) (K₀) d order shelf op.count (physical) F (rate))(x:Wallet (A)):
    WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books hi ahead (S₀) (e₀) ((physical) x) where
  grades:=d
  order:=order
  shelf:=shelf
  seats:=op.count
  law:=physical
  post:=F
  appointment:=book
  x:=x
  atInput:=rfl

include simple course cut cal hospital chamber in
theorem original
    (fit:∀j,rank R d (entry R d j (q j)) ≤ order)(slots:Fintype.card V ≤ op.count)
    (space:∑j,d j ≤ shelf)(level:shelf ≤ R.alloy.B.a.clock.J i)
    (ord:order ≤ R.alloy.B.a.clock.J i)(stage:order+1 ≤ op.stage)
    (count:op.count ≤ Burn.horizon k+2)(cap:order+(∑j,d j) ≤ Burn.horizon k+2)
    {tol:ℝ}(tp:0 < tol)(x₀:Wallet (A))
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i)
    (p:ℕ)(way:WayStation R.kit)(hardFloor:6*op.count ≤ R.alloy.B.a.clock.J i)
    (deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged (by norm_num:0<(1:ℝ)) ≤ i)
    (more:WilsonMeasuredSemesterSubpower.onset R op.count (by norm_num:0<(1:ℝ)) ≤ i)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ i+1)
    (fresh:(eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple
      (Fintype.card V) (order+shelf+1+(D₀)) ((D₀)+2))).choose ≤ i):
    ∃F:Ptype,F.passport=Passport.point o ∧ F.inputIndex=Empty ∧ F.op=op ∧ F.lesson=lesson ∧
      F.modelIndex=V ∧ HEq F.model M ∧
      F.input.hard.Paid F.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      8*(budgetR R i)^op.count*F.rent ≤ tol ∧
      (∀j,(F.w j)⁻¹ ≤ max 1 (C₀)*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2))) ∧
      Nonempty (WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (A) (K₀)
        d order shelf op.count (physical) F (rate)) ∧
      (∀x,(Tint.Patrol.picture F.model F.input).density x=(physical) x) ∧
      ∀{h:V→ℕ}(κ:(j:V)→Knob (h j))(pt:V→Chamber)(x:Wallet (A))
        (U:Config G (R.family.side (i+1) per))(s:(marks).Mode),
        (((Tint.Patrol.picture F.model F.input).density x U).part s)/((H).eval U:ℂ)=
          ∏j∈s.val,probe j x*WilsonReceivedCanonicalVerseBasis.restored R d κ pt
            (regulatorRun R.family N per (i+1)) j (q j) (o j) U:=by
  obtain ⟨F,site,empty,event,weather,names,ink,hard,rented,wallet,field,amount⟩:=
    WilsonOriginalCensusCanonicalPost.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson cal
      ahead chamber hospital d q hd o order shelf fit slots space level ord stage count cap tp x₀ atBare warm pass halo onset
  have paid:=booked R simple hk D Q π Γ Ψ course books hi cut op ahead hospital d q hd o order shelf
    F site names ink event wallet count level pass onset p way hardFloor deep aged opened more cooled fresh
  exact ⟨F,site,empty,event,weather,names,ink,hard,rented,wallet,paid,field,amount⟩

end YM.Integration.WilsonOriginalCensusCanonicalFiled
end
