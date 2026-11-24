import YM.Integration.WilsonOriginalMeasuredReentry
import YM.Integration.WilsonMovingMentorIncomingSlots
import YM.Integration.WilsonMixedWalletFiledInput
import YM.Integration.WilsonOriginalFreshQWallet
import YM.QuadraticLocal.Class.Foundry
import YM.QuadraticLocal.Rebirth.Press

/-! The original outgoing marked coefficients in the next measured coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedQFiled

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth
open Source Labels ActualOriginalQReaders ActualOriginalQPackets WilsonOriginalProjectedCurvaturePassport
open QuadraticLocal.Affinity ConnectedActivityE6 LocalComparison
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

include course cut in
theorem received (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (load:op.count ≤ Burn.horizon k+2)
    (cost:ℝ) (issued:Scene.Armada M₁ w grades scale cost order op.count shelf)
    (school:Tableau pieces₀ actors M₁)
    (h:ℝ) (one:1 ≤ h) {regular hard ν gross:ℝ}
    (rawBirth:WilsonOriginalFreshQWallet.Return qborn site labels offset orders N scale extra actors pieces₀ priorHome
      old fresh apart (H).p wQ jointRad ν gross)
    (signed:WilsonOriginalBornLedger.priced H joint (Stock.census V) A₂ K₂ born initial jointRad (Stoop.radius jointRad h) regular hard raw)
    (positiveNew:∀v,0<wQ v) (fit:∀v∈old,jointRad v ≤ w v)
    {qCost:ℝ} {qOrder qLoad qShelf:ℕ}
    (jointPaid:Scene.Armada full jointRad grade scale qCost qOrder qLoad qShelf) :
    ∃ (c:Type),Countable c ∧ ∃ next:Tint.Incoming joint H (Wallet A₂) c (Stock.census V),
      Scene.Armada full (Stoop.radius jointRad h) grade scale (h⁻¹*qCost) qOrder qLoad qShelf ∧
      Tableau K₂ A₂ full ∧ next.old.Paid (Stoop.radius jointRad h) (H).p.B width
        (h⁻¹*((fig).fidelity*stampFee*cost+regular)) ∧
      next.hard.Paid (Stoop.radius jointRad h) (H).p.B (H).p.supportExponent hard ∧
      Taut (joint).support A₂ K₂ next.old ∧ Crown (joint).support A₂ K₂ next.hard ∧
      (∀x U,(Tint.Patrol.picture full next).density x U=Poly.pass (rawQ x U)*(raw x U)) ∧
      ∀x U,((Tint.Patrol.picture full next).density x U).part (Stock.census V).quiet=((H).eval U:ℂ) := by
  have calibrated:=(WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut lesson books op ahead
    month order shelf fits narrow).1
  let paidWalk:=(WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  have upperBand:(Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [(course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta]
    exact (R.makes.wilson.represents N per (i+1) cut).band
  have upper:=(Mentor.Cruise.Semester.tight D R.rolls Q R.alloy R.kit φ books pass op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter ahead
    (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).truep.point paidWalk
    (course.1.walk i hi cut.le).truep.point hospital load shelf narrow upperBand).2.soon
  have lower:=WilsonOriginalMeasuredReentry.connected R hk D Q pass π Γ Ψ course hi cut lesson books op ahead
    month order shelf hospital voter.height narrow load
  have lawful:=(course.1.walk i hi cut.le).truep.valid.labels
  let cash:=Hard.rentValid lawful.forced lawful.boundK
  let hh:Hard (Wallet actors) (H).p (H).activities.forced (H).activities.K (priorHome).origin (Stock.census V):=Hard.rent cash
  have native:Crown (priorHome).support actors pieces₀ hh:=by
    refine ⟨fun l U=>Affinity.Stencil.const (Poly.bead (Stock.census V) (↑((H).activities.K l U):ℂ)) fun z ne=>?_⟩
    exact (Poly.part_send ..).trans (if_neg ne)
  haveI countStudent:Countable (Scene.Texts M (sheet).ratio (Mentor.Cruise.publish D R.rolls Q R.alloy φ books op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry)):=Scene.crewC M (sheet).ratio (Mentor.Cruise.publish D R.rolls Q R.alloy φ books op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry)
    (Mentor.Cruise.funded D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry
      lesson.studied ahead)
  have seated:=(@WilsonMixedWalletMeasuredRestamp.measured G _ V _ _ _ _ countStudent) priorHome siteHome H (Stock.census V) actors freshA pieces₀ freshK
    old zeroA born M₁ (Γ i) ζ depth order oldG newG w jointRad (Stoop.radius jointRad h) grades calibrated issued
    upper lower.soon lower.bloom.le school jointPaid.positive fit hh native rawBirth.posted.salary raw signed
  have enrolled:=Mutation.allocate M₁ (Γ i) ζ depth order w grades calibrated issued
  have past:=Scene.Armada.paid stamped w grades enrolled (H).p lower.soon
  have gauge: Pert.Asymptotics.regulatorRun R.family N per i = newG:=by
    unfold Pert.Asymptotics.regulatorRun Coat.gStep
    rw [(course.1.walk i hi cut.le).beta]
    rfl
  have orig:=rawBirth.original
  rw [gauge] at orig
  have surplus:=WilsonOriginalFreshQCover.raised (rendered rows (H).p newG) wQ positiveNew orig
    (fun _=> Finset.le_sup (f:=fun s=>Lattice.coverNumber (H).p.B ((rendered rows (H).p newG).ground s)) (Finset.mem_univ _))
  have same x U:=rawBirth.masked x U
  simp only [gauge] at same
  obtain ⟨c,counted,post,finance,tabs,reg,force,hit,halo,reading,quiet⟩:=
    WilsonMixedWalletFiledInput.received H actors freshA pieces₀ freshK old fresh apart zeroA (WilsonOriginalMixedTestTableau.zero site)
      born stamped rows h one hh native seated.2 (WilsonOriginalProjectedCurvatureTableau.real site qborn labels offset orders N scale extra)
      issued.positive positiveNew past surplus rawBirth.posted.salary fit same raw seated.1 jointPaid lower.soon
  exact ⟨c,counted,post,finance,tabs,reg,force,hit,halo,fun x U=>(reading x U).trans (by rw [rawBirth.posted.source]),quiet⟩
end YM.Integration.WilsonOriginalSignedQFiled
