import YM.Integration.WilsonOriginalDepositedModelBook
import YM.Integration.WilsonIndependentCollarSharpPost

/-! The printed finite marked roster and the genuine numerical return are issued together. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSharpBook
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

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

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Filter MintClock Multi
local notation "H" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))

open WilsonOlderFreshGraphSlate
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
    (passport:Earn.Passport (R.family.side (i+1) per) V)
    (B:I→Earn.Binder passport (Stock.census V)) (grades:V→ℕ)
    (order shelf q:ℕ) (H₀:V→ℝ) (budget:I→ℝ)
local notation "dₛ" z:max => (∑v∈(B z).mode.val,grades v)
variable (T:∀z:I,Copy G (∑v∈(B z).mode.val,grades v) q
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))))
local notation "point" z:max => WilsonOlderFreshGraphPointWallet.point (B z).center
local notation "A" => WilsonOriginalMixedBlockRows.room V
local notation "K₀" => (fun _:V=>(⊥:Submodule ℝ ℂ))
local notation "gf" => Coat.gStep (H).beta
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "D₀" => (∑v:V,grades v)+1
local notation "ink" z:max y:max U:max => ∑'h:(T z).Roster,
  WilsonGeneralArityCopyAccount.term (T z) (B z).center y U h
local notation "value" z:max y:max x:max U:max => (∏v∈(B z).mode.val,(x v).val)*(ink z y U)
local notation "law" => fun (x:Wallet (A))(U:Config G (R.family.side (i+1) per))=>
  ((H).eval U:ℂ) • ∏z:I,(1+Poly.send (B z).mode (value z (gf) x U))
local notation "Ftype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  (A) (K₀) grades order shelf op.count i hi (law)
local notation "gain" => WilsonOriginalMixedBlockBudget.roots B budget
local notation "tickets" => fun v=>H₀ v*max 1 (gain)
local notation "base" => fun v=>(H₀ v)⁻¹
local notation "marks" => Stock.census V
local notation "pupil" F:max => Oak.student (n:=per) R hk D Q π Γ books hi (F).op (F).lesson
  ahead (A) (F).model order (F).voter

include simple course cut hospital cal chamber in
theorem original (qfit:q ≤ order) (occupied:1 ≤ op.count)
    (size:∀v,0 < H₀ v) (paid:∀z,Real.exp ((σ₀)*(B z).length)*(WilsonIndependentCollarSlateIntensity.amount (T z) (B z).center) ≤
      Poly.toll H₀ (B z).mode*budget z) (slots:Fintype.card V ≤ op.count) (count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v,grades v) ≤ shelf) (level:shelf ≤ R.alloy.B.a.clock.J i) (stage:order+1 ≤ op.stage)
    (expense:order+(∑v,grades v) ≤ Burn.horizon k+2)
    {tol:ℝ} (tp:0 < tol) (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i)
    (p:ℕ) (way:WayStation R.kit) (hardFloor:6*op.count ≤ R.alloy.B.a.clock.J i)
    (deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged
      (by norm_num:0<(1:ℝ)) ≤ i)
    (more:WilsonMeasuredSemesterSubpower.onset R op.count (by norm_num:0<(1:ℝ)) ≤ i)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ i+1)
    (fresh:(eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple
      (Fintype.card V) (order+shelf+1+(D₀)) ((D₀)+2))).choose ≤ i) :



    ∃F:Ftype, F.passport=passport ∧ F.inputIndex=Empty ∧ F.op=op ∧ F.lesson=lesson ∧
      F.modelIndex=((z:I)×(T z).Roster) ∧
      HEq F.model (WilsonOriginalMixedBlockRows.mounted B (fun z:I=>(T z).rows (point z) disk)) ∧
      F.input.hard.Paid F.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      (8*(budgetR R i)^op.count)*F.rent ≤ tol ∧
      (∀v,(F.w v)⁻¹ ≤ (tickets) v*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2))) ∧
      Nonempty (WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (A) (K₀) grades
        order shelf op.count (law) F (fun s=>(R.alloy.B.a.clock.hatBeta i)^(((D₀)+5)*(Fintype.card V))*Poly.toll (tickets) s)):=by
  have priced:=WilsonOriginalMixedBlockBudget.original B (σ₀) (fun z=>WilsonIndependentCollarSlateIntensity.amount (T z) (B z).center) budget H₀ size paid
  obtain ⟨F,site,blank,event,weather,idx,same,hard,rent,fee,source,_⟩:=
    WilsonIndependentCollarSharpPost.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson cal ahead
      chamber hospital passport B grades order shelf q (base) T qfit occupied (fun v=>inv_pos.mpr (size v))
      slots count fit level stage expense tp warm atBare pass halo onset
  have upper:∀v,(F.w v)⁻¹ ≤ (tickets) v*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2)):=by
    intro v
    have h:=fee v
    simp only [inv_inv] at h
    have χp:0 ≤ χ:=zero_le_one.trans (R.alloy.B.a.fits.delayed _).le
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (max_le_max_left 1 priced) (size v).le)
      (by positivity))
  have positive:0 < (gf):=by
    rw [(course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have field:=WilsonOriginalFreshJoinedRows.posted F.model (H).p (gf) (H).eval (fun z=>(B z).mode)
    (fun z=>⟨(B z).front,(B z).east⟩) (fun z t U=>value z (gf) t U) (source (gf) positive)
  have paidRows (t:Wallet (A)) : ∃row:WilsonOriginalOccupiedWindow.Slice R (marks) (Ψ i),
      row.w=F.w ∧ row.hard=1 ∧ WilsonOriginalOccupiedSalary.debit row.regular row.hard ≤ 10*χ ∧
      (∀s:(marks).Mode, (WilsonOriginalOccupiedSalary.debit row.regular row.hard)^s.val.card ≤
        (R.alloy.B.a.clock.hatBeta i)^(((D₀)+5)*(Fintype.card V))*(Poly.toll (tickets) s*Poly.toll row.w s)) ∧
      row.A.density row.x=LocalComparison.actualPush R.family N per i ((law) t) ∧
      row.A.E.log row.x=((rendered (pupil F) (Ψ i).p (gf)).join F.output.old).log t:=by
    have co:F.op.count=op.count:=congrArg _ event
    have funded:∀s:(marks).Mode,(∑v∈s.val,grades v)+1 ≤ (D₀):=fun _=>Nat.succ_le_succ
      (sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ _) (fun _ _ _=>Nat.zero_le _))
    obtain ⟨row,ww,reg,hr,whole,lamps,_⟩:=WilsonOriginalOccupiedFiledSlice.original R hk D Q π Γ Ψ
      books hi cut ahead (A) (K₀) grades order shelf op.count (law) F simple way course (D₀) p funded
      hardFloor deep aged (by norm_num:0<(1:ℝ)) (by simpa only [co] using opened) t
    have cold:=(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec (i+1)
      cooled N per cut
    have small:Pert.Asymptotics.regulatorRun R.family N per (i+1) ≤ 1:=by linarith only [cold.1,cold.2]
    have served:=WilsonOriginalOccupiedFiledFare.original R hk D Q π Γ Ψ course books hi cut ahead
      (A) (K₀) grades order shelf op.count (law) F pass hospital level (by simpa only [co] using count)
      onset (by simpa only [co] using more) F.small p 1 (by
        rw [one_mul]; change (Pert.Asymptotics.regulatorRun R.family N per (i+1))^p ≤ 1
        exact pow_le_one₀ cold.1.le small)
    have debit:WilsonOriginalOccupiedSalary.debit row.regular row.hard ≤ 10*χ:=by simpa only [reg,hr] using served
    obtain ⟨_,_,_,_,joint⟩:=WilsonOriginalFreshJoinedRows.earned R hk D Q π Γ Ψ books hi cut ahead
      (A) (K₀) grades order shelf op.count (law) F simple way course (D₀) p funded hardFloor deep aged
      (by norm_num:0<(1:ℝ)) (by simpa only [co] using opened) t
    refine ⟨row,ww,hr,debit,?_,whole,funext fun U=>(lamps U).trans (joint U).symm⟩
    intro s
    apply (eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple (Fintype.card V)
      (order+shelf+1+(D₀)) ((D₀)+2))).choose_spec i fresh s (Finset.card_le_univ s.val) row.w
      row.positive (tickets) (zero_le_one.trans (le_max_left ..)) debit
      (fun v=>mul_pos (size v) (zero_lt_one.trans_le (le_max_left ..)))
    simpa only [ww] using upper

  choose row radius resident height fare received joined using paidRows
  refine ⟨F,site,blank,event,weather,idx,same,hard,rent,upper,⟨{
    declared:=field
    row:=row
    radius:=radius
    resident:=resident
    height:=height
    wage:=?_
    density:=received
    mounted:=joined }⟩⟩
  intro t s
  exact (fare t s).trans_eq (mul_assoc ..).symm

end YM.Integration.WilsonIndependentCollarSharpBook
end
