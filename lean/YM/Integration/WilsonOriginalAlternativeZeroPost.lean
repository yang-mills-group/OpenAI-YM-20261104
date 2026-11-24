import YM.Integration.WilsonOriginalAlternativeQuietPost
import YM.Integration.WilsonOriginalAlternativeTrialFunded
import YM.Integration.WilsonMeasuredOwnerReserve

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeZeroPost
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonReceivedFirstTrace
open WilsonMeasuredCourseSourceGerm
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {m N per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,Rep G (R.family.side j per))
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type} [Fintype V] [DecidableEq V] (grades:V→ℕ) (order shelf seats:ℕ)
  (floor:m ≤ i) (cut:i < N)
local notation "D_" => WilsonOriginalAlternativeFiniteSource.disks (V:=V)
local notation "K_" => WilsonOriginalAlternativeFiniteSource.sectors (V:=V)
local notation "J_" => Stock.census V
local notation "W_" => Ψ (i+1)
local notation "κ_" => LocalComparison.forcedDivisor R.family (i+1)
local notation "a_" => R.family.path.levels.clock.forcedAllowance (i+1)
variable (reg:Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead
    (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) shelf seats)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ floor)
  (o:V→Site (R.family.side (i+1) per))
local notation "zone_" => Passport.point o
local notation "model_" => (Empty.elim:Empty→Row zone_ J_ G (Wallet D_))
local notation "source_" => (fun (_:Wallet D_) (U:Config G (R.family.side (i+1) per))=>
    ((W_).eval U:ℂ) • Poly.pass (0:Poly J_))

include reg cut in
/-- The true quiet field seats every requested grade on the already appointed course. -/
theorem original (shape:op.count=seats) (slots:Fintype.card V ≤ op.count)
    (space:(∑v,grades v) ≤ shelf) (pace:order+1 ≤ op.stage):
    ∃P:Post (N:=N) R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats i floor source_,
      Countable P.inputIndex ∧ P.modelIndex=Empty ∧ P.inputIndex=Empty ∧
      P.passport=zone_ ∧ P.op=op ∧ P.lesson=lesson ∧ P.cost=0 ∧ P.rent=1 ∧ P.w=(fun _=>1) ∧
      ∀x j U,P.input.hard.hard x j U=Poly.bead J_ (((W_).activities.K j U:ℝ):ℂ):=by
  let ok:=(later R π Γ Ψ reg.course (floor.trans i.le_succ) cut).truep.valid.labels
  let raw:Hard.Rent (W_).activities.forced (W_).activities.K (W_).p (W_).p.supportExponent a_:=
    Hard.rentValid ok.forced ok.boundK
  let Z:=WilsonPhysicalMarkedDefect.modelInput zone_ (W_) J_ (Wallet D_) raw
  let w:V→ℝ:=fun _=>1
  have wp:∀v,0 < w v:=fun _=>zero_lt_one
  have brief:Scene.Ministry J_ grades op.count shelf:=by
    refine ⟨fun s=>?_,fun s=>?_⟩
    · exact (show s.val.card ≤ Fintype.card V by simpa using s.val.card_le_univ).trans slots
    · exact (Finset.sum_le_sum_of_subset (Finset.subset_univ s.val)).trans space
  let σ:=Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
  have salary:Scene.Armada model_ w grades σ 0 order op.count shelf:=by
    refine ⟨brief,wp,fun _=>?_,⟨fun j=>j.elim,fun j=>j.elim⟩,fun j=>j.elim⟩
    exact ⟨fun j=>j.elim,Summable.of_finite,by simp⟩
  have vote:Cruise.Voter model_ σ order op.count op.stage k (R.alloy.B.a.clock.J i):=by
    refine ⟨fun j=>j.elim,brief.quota,pace,fun C=>?_⟩
    obtain ⟨j,-⟩:=C.property.1
    exact j.elim
  have test:Tableau K_ D_ model_:=⟨fun j=>j.elim⟩
  obtain ⟨taut,crown⟩:=WilsonPhysicalMarkedDefect.model_input_addresses (A:=zone_) (Γ:=J_) D_ K_ raw
  have weak:=Z.old.loan_monotone (Spill.Foundry.empty_lit (W_) Z (W_).p.supportExponent (W_).p.B (w:=w)) zero_le_one
  have strong:=Z.old.loan_monotone (Spill.Foundry.empty_lit (W_) Z ((W_).p.supportExponent+1+1) (W_).p.B (w:=w)) zero_le_one
  have sq:κ_^2=a_:=Real.sq_sqrt (Real.exp_pos _).le
  have one:κ_ ≤ 1:=(Graces.glyphBound R.alloy.B.a (i+1)).2
  have native:a_ ≤ κ_:=by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ κ_ from Real.sqrt_nonneg _) (sub_nonpos.mpr one)]
  have hard:=Hard.mono Z.hard (WilsonPhysicalMarkedDefect.model_input_prices (A:=zone_) (Γ:=J_) raw w).2 native
  let cal:=Classical.choice (Oak.agrees R hk D Q π Γ Ψ reg.course floor cut lesson)
  have narrow:=reg.narrow.trans (R.alloy.B.a.fits.mono floor)
  obtain ⟨I,count,out,story⟩:=Oak.Buffered.arrive R reg.simple hk D Q π Γ Ψ reg.course reg.scroll books reg.chamber
    floor cut op lesson cal ahead reg.hospital D_ K_ model_ Z w grades order shelf vote 1 0
    (shape.trans_le reg.load) narrow salary test reg.test taut crown weak (Hard.mono _ hard one)
    zero_le_one zero_lt_one le_rfl
  have represented (x:Wallet D_) (U:Config G (R.family.side (i+1) per)):
      (Tint.Patrol.picture model_ Z).density x U=((W_).eval U:ℂ) • Poly.pass (0:Poly J_):=by
    have field:=WilsonOriginalAlternativeQuietShelf.field D_ zone_ (W_) raw Z.old wp weak x U
    have zero:Z.old.log x U=0:=tsum_empty
    exact field.trans (congrArg (fun t:Poly J_=>((W_).eval U:ℂ) • Poly.pass t) zero)
  let P:Post (N:=N) R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats i floor source_:=
    ⟨op,shape,lesson,zone_,Empty,Empty,I,inferInstance,count,model_,Z,out,w,0,1,
      inv_nonneg.mpr (zero_le_one.trans story.Waffle.cool),zero_lt_one,le_rfl,vote,salary,test,taut,crown,
      strong,hard,fun x=>funext (represented x),story⟩
  refine ⟨P,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · change Countable Empty
    infer_instance
  · intro x j U
    rfl

end YM.Integration.WilsonOriginalAlternativeZeroPost
end
