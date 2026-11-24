import YM.Integration.WilsonOriginalMeasuredReentry
import YM.Integration.WilsonOriginalSignedWalletCourse
import YM.Integration.WilsonOriginalSignedQFiled
import YM.Integration.WilsonMovingMentorIncomingSlots
import YM.Integration.WilsonMixedWalletFiledInput
import YM.Integration.WilsonOriginalFreshQWallet
import YM.QuadraticLocal.Class.Foundry
import YM.QuadraticLocal.Rebirth.Press

/-! The original outgoing marked coefficients in the next measured coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedQAdmission

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth
open Source Labels ActualOriginalQReaders ActualOriginalQPackets WilsonOriginalProjectedCurvaturePassport
open QuadraticLocal.Affinity ConnectedActivityE6 LocalComparison Graces
open WilsonMixedTestTableau WilsonMixedPassportRows
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)] [Countable ι]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport (Stock.census V) G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))

local notation "M₁" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ hi lesson
local notation "depth" => Burn.horizon k+2
local notation "level" => (show Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i from hk.trans (R.alloy.B.a.fits.mono hi))
local notation "book" => (litP D R.alloy Q level lesson.entry)
local notation "filed" => (book).issue lesson.entry
local notation "zeroFiled" => ((book).sustenance.due lesson.entry).1
local notation "stamped" => Mutation.stamp M₁ (Γ i) ζ depth order
local notation "T₀" => AllOrder.Floe.Step.tape depth
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)


variable {B:MS.Local.Physical.Deck G} (qborn:MS.Land.Prescription B)
  {report:ℕ} {live:report ≤ i} (site:ActualRunQlocalNativeTuple.Datum R per i report live V)
  (labels:V → MS.Rake.Label B) (offset:ℝ) (orders extra:V → ℕ)
  (pieces₀:∀ v,Submodule ℝ (X v)) (old fresh:Finset V) (apart:Disjoint old fresh)
  (zeroA:∀v,0∈actors v) (jointRad wQ:V → ℝ) (grade:V → ℕ)
  {u0:Type} (before:Tint.Incoming passport (Ψ (i+1)) (Wallet actors) u0 (Stock.census V))
local notation "H" => Ψ i
local notation "siz" => (R.alloy.B.a.S.oneStep i per).exact_size
local notation "sheet" => Pane.panel R.alloy i siz
local notation "priorHome" => passport.coarser (sheet).ratio
local notation "siteHome" => paper site labels
local notation "joint" => WilsonMixedPassportRows.passport (owner priorHome siteHome old)
local notation "freshA" => WilsonOriginalProjectedCurvatureTableau.actors site
local notation "freshK" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls site v).restrictScalars ℝ)
local notation "A₂" => WilsonMixedTestTableau.actors actors freshA
local notation "K₂" => pieces pieces₀ freshK
local notation "rightTest" => right actors freshA fresh (WilsonOriginalMixedTestTableau.zero site)
local notation "leftTest" => left actors freshA old zeroA
local notation "rows" => WilsonOriginalProjectedCurvatureLamps.cohort qborn site labels offset orders N scale extra
local notation "born" => WilsonOriginalReceivedFreshQ.birth qborn site labels offset orders N scale extra actors priorHome old fresh apart (H).p
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "newG" => Coat.gStep (H).beta
local notation "initial" => WilsonMixedReceivedLamp.regular (P:=priorHome) (Q:=siteHome) (W:=H) actors freshA old zeroA (rendered M₁ (H).p oldG)
local notation "full" => WilsonMixedFaceLog.routed stamped rows old fresh apart leftTest rightTest
local notation "width" => ((H).p.supportExponent+1+1)
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "raw" => fun x => (sheet).push (Ψ (i+1)).beta ((Tint.Patrol.picture M before).density (leftTest x))
local notation "rawQ" => (fun x U=>MergeProof.Accent.Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader site v (testInclusion (ActualRunQlocalNativeTuple.orbit site) (rightTest x) v) *
  ActualOriginalCalibratedColumns.weightedObservable R B qborn (labels v) offset (R.family.side i per)
    (ActualRunQlocalNativeTuple.root site v) U (orders v)))
local notation "stampFee" => Invoice.price (H).p (fig).mist (order+shelf+1) op.count width (fig).limitC G


variable (simple:G.Simple) [Countable u0] (education:Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
variable {b e ν gross qCost:ℝ} {qOrder qLoad qShelf:ℕ}
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "ratio" => (sheet).ratio
local notation "cost" => (fig).produce (ratio).count*b
local notation "δ" => Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k
local notation "residue" => (fig).hitPrice G (ratio).count (Ψ (i+1)).p (H).p b e δ oldG
local notation "bill" => (fig).fidelity*stampFee*cost+residue
local notation "fare" => books.salary (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i) op
local notation "β₀" => R.alloy.B.a.clock.hatBeta i
local notation "slip" => QuadraticLocal.Shelter.Deck.crewCost (fig).helmet ((H).p.supportExponent+1) (fig).bearing*
  (((fare).enroll β₀)^op.count*((fare).price β₀)+(fig).grow G (ratio).count (H).p b+(fig).pay (ratio).count (H).p b)
local notation "slack" => Willow.haloSlack (R.alloy.B.a.budget i).B
local notation "hard" => Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta
local notation "h" t:max => WilsonRootedKioskFreeRadius.radius (max (bill/t) qCost) slip gross slack
local notation "Ω₀" => QuadraticLocal.Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "money" => (Pressure.betaF G β₀ (R.rolls.L (R.alloy.B.a.clock.J (i+1)))) ^ Mentor.Tuition.need order (Mentor.Tolerance (R.alloy.B.a.clock.J i))

include course cut simple education in
theorem received (pass:Pass D Q R.alloy R.kit) (way:WayStation R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (narrow:shelf ≤ R.alloy.B.a.clock.J i)
    (load:op.count ≤ Burn.horizon k+2) (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
    (x₀:Wallet actors) (phase:0<e) (bound:e ≤ 1) (farePaid:b ≤ Ω⁻¹)
    (notes:Scene.Armada M w grades Ω₀ b order op.count shelf) (school:Tableau pieces₀ actors M)
    (earlier:before.old.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent e)
    (forced:before.hard.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent 1)
    (basis:Taut passport.support actors pieces₀ before.old) (cover:Crown passport.support actors pieces₀ before.hard)
    (rawBirth:WilsonOriginalFreshQWallet.Return qborn site labels offset orders N scale extra actors pieces₀ priorHome
      old fresh apart (H).p wQ jointRad ν gross)
    (positiveJoint:∀v,0<jointRad v) (positiveNew:∀v,0<wQ v) (fit:∀v∈old,jointRad v ≤ w v)
    (jointPaid:Scene.Armada M₁ w grades scale (cost) order op.count shelf →
      Scene.Armada full jointRad grade scale qCost qOrder qLoad qShelf)
    (tolerance:ℝ) (pt:0<tolerance) :
    let h₁:=h tolerance
    (h₁⁻¹*qCost ≤ 1) ∧ h₁⁻¹*(bill) ≤ tolerance ∧ hard ≤ forcedDivisor R.family i ∧
      hard ≤ 1 ∧ residue ≤ 8*Ω*(e+δ+money) ∧
      h₁ ≤ max (max 1 (max (bill/tolerance) qCost)) (Ω^5+gross/slack) ∧
      ∃ (c:Type),Countable c ∧ ∃ next:Tint.Incoming joint H (Wallet A₂) c (Stock.census V),
        Scene.Armada full (Stoop.radius jointRad h₁) grade scale (h₁⁻¹*qCost) qOrder qLoad qShelf ∧
        Tableau K₂ A₂ full ∧ next.old.Paid (Stoop.radius jointRad h₁) (H).p.B width (h₁⁻¹*(bill)) ∧
        next.hard.Paid (Stoop.radius jointRad h₁) (H).p.B (H).p.supportExponent hard ∧
        Taut (joint).support A₂ K₂ next.old ∧ Crown (joint).support A₂ K₂ next.hard ∧
        (∀x U,(Tint.Patrol.picture full next).density x U=Poly.pass (rawQ x U)*(raw x U)) ∧
        ∀x U,((Tint.Patrol.picture full next).density x U).part (Stock.census V).quiet=((H).eval U:ℂ) := by
  intro t
  let r:=max (bill/tolerance) qCost
  have one:1 ≤ t:=(le_max_left 1 r).trans (le_max_left _ _)
  have ample:r ≤ t:=(le_max_right 1 r).trans (le_max_left _ _)
  have ht:0<t:=zero_lt_one.trans_le one
  have a:t⁻¹*qCost ≤ 1:=by
    rw [←div_eq_inv_mul,div_le_one ht]
    exact (le_max_right _ _).trans ample
  have d:t⁻¹*(bill) ≤ tolerance:=by
    rw [←div_eq_inv_mul,div_le_iff₀ ht]
    simpa only [mul_comm tolerance t] using (div_le_iff₀ pt).mp ((le_max_left _ _).trans ample)
  have covered:=WilsonOriginalSignedWalletCourse.original R simple actors pieces₀ D Q φ books pass education op
    (Oak.era R hk D Q π Γ hi op lesson) lesson.entry lesson.studied course hi cut M w notes.positive voter before x₀ ahead
    hospital load narrow grades phase bound freshA freshK siteHome old zeroA jointRad born r farePaid notes
    cal.seeds cal.candor earlier forced school basis cover positiveJoint fit rawBirth.posted.salary rawBirth.posted.full rawBirth.posted.affine
  have flat:=QuadraticLocal.Advent.force_bill R way π Γ Ψ course hi cut (Nat.zero_le _)
  have fl:hard ≤ forcedDivisor R.family i:=by simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] using flat
  have issued:=WilsonOriginalSignedQFiled.received R hk D Q π Γ Ψ course books hi cut op lesson ahead actors M w grades order shelf voter
    qborn site labels offset orders extra pieces₀ old fresh apart zeroA jointRad wQ grade before pass month hospital fits narrow load
    (cost) covered.2.1 covered.2.2.1 t one rawBirth covered.1 positiveNew fit (jointPaid covered.2.1)
  exact ⟨a,d,fl,fl.trans (Graces.glyphBound R.alloy.B.a i).2,covered.2.2.2.1,covered.2.2.2.2,issued⟩
end YM.Integration.WilsonOriginalSignedQAdmission
