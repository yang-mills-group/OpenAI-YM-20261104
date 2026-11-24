import YM.Integration.WilsonOriginalSignedWalletSemester
import YM.Integration.WilsonOriginalProjectedCurvatureCourseNotice

/-! The marked withdrawal on the elected unmodified physical course. The fine
and coarse representatives and both merger tapes are obtained from its history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalSignedWalletCourse
open Function Finset Filter Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP PhysicalNext.Repeat.Boulevard
open AnalyticBridge VerifiedReset QuadraticLocal.Mentor ConnectedActivityE6
open WilsonMixedTestTableau WilsonMixedPassportRows
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
  {V ι ιw:Type} [DecidableEq V] [Fintype V] [Countable ι] [Countable ιw]
  {Film:V → Type} [∀v,AddCommGroup (Film v)] [∀v,Module ℝ (Film v)]
  (Actor:∀v,Set (Film v)) (pieces:∀v,Submodule ℝ (Film v))
  (root:PlanV.Roots («G»:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (table:root.Tab R.rolls) (ψ:ℕ → ℕ) (books:Mentor.Offices.Books root R.rolls table ψ)
  (pass:Pass root table R.alloy R.kit)
  (education:Mentor.Educated root R.rolls table R.kit.shape R.kit.scout ψ books R.alloy.delay)
  {first m N per order:ℕ} {π:ℕ → Layout G} {Γ:ℕ → Pace.Coin}
  {H:(s:ℕ) → Rep G (R.family.side s per)}
local notation "J" => R.alloy.B.a.clock.J
variable (op:Mentor.Opportunity (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
  (epoch:Mentor.Epoch root R.rolls (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) op)
  (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
  (journey:PlanV.Journey root R.alloy («N»:=N) («m»:=m) card) (upper:π (m+1)=card.extra)
  (course:Concourse R.alloy R.kit R.T π Γ first N per epoch.vac H)
  (start:first  ≤  m) (before:m < N)
  {D:Passport (R.family.side (m+1) per) V} {ρ:Census V}
  (M:ι → Row D ρ G (Affinity.Wallet Actor)) (w:V → ℝ) (positive:∀j,0<w j)
  (voter:Mentor.Cruise.Voter M (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))
    order op.count op.stage epoch.vac (R.alloy.B.a.clock.J m))
  (input:Tint.Incoming D (H (m+1)) (Affinity.Wallet Actor) ιw ρ)
  (y:Affinity.Wallet Actor)

variable {v:ℕ} (forecast:Mentor.Forecast root R.rolls table ψ books)
  (hospital:MintClock.Hospital root R.rolls table R.kit.target ψ books forecast R.alloy.delay)
  (load:op.count ≤ Burn.horizon epoch.vac+2) (rank:v ≤ R.alloy.B.a.clock.J m)
  (T:V → ℕ) {b e:ℝ} (phase:0<e) (full:e ≤ 1)
local notation "u" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "ratio" => (Pane.panel R.alloy m u).ratio
local notation "Ω" => Mentor.Cruise.Semester.expense root R.rolls table R.alloy R.kit ψ books op epoch order forecast v
local notation "E" => Mentor.Cruise.Semester.figure root R.rolls table R.alloy R.kit ψ books op epoch order forecast v
local notation "filed" => Mentor.Cruise.publish root R.rolls table R.alloy ψ books op epoch u M order voter card
local notation "bank" => Mentor.Cruise.funded root R.rolls table R.alloy ψ books op epoch u M order voter card journey forecast
local notation "model" => WilsonRootedKioskOccupiedSlip.bare
  (Width.treasured M ratio filed bank (H m).p (E).afterwards (Coat.gStep (H (m+1)).beta))
local notation "β₀" => R.alloy.B.a.clock.hatBeta m
local notation "β₁" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "δ" => Burn.young β₁ epoch.vac
local notation "income" => (Pressure.betaF G β₀ (R.rolls.L (J (m+1)))) ^ Mentor.Tuition.need order (Mentor.Tolerance (J m))
local notation "slack" => Willow.haloSlack (R.alloy.B.a.budget m).B
local notation "frozen" => Time.quoteHard R.alloy.B.a m R.kit.book (H (m+1)).beta
local notation "atFine" => course.1.walk (m+1) (Nat.le_succ_of_le start) before
local notation "atCoarse" => course.1.walk m start before.le
local notation "intake" => WilsonMovingMentorIncomingSlots.original R course start before


local notation "filedRows" => Scene.letters M ratio filed bank (E).afterwards
local notation "beforeRows" => Width.treasured M ratio filed bank (H m).p (E).afterwards (Coat.gStep (H (m+1)).beta)
local notation "residue" => (E).hitPrice G (ratio).count (H (m+1)).p (H m).p b e δ (Coat.gStep (H (m+1)).beta)
local notation "fare" => books.salary (J (m+1)) (J m) op
local notation "slip" => QuadraticLocal.Shelter.Deck.crewCost (E).helmet ((H m).p.supportExponent+1) (E).bearing*
  (((fare).enroll β₀)^op.count*((fare).price β₀)+(E).grow G (ratio).count (H m).p b+(E).pay (ratio).count (H m).p b)
variable {Film₁:V → Type} [∀v,AddCommGroup (Film₁ v)] [∀v,Module ℝ (Film₁ v)]
  (freshA:∀v,Set (Film₁ v)) (freshK:∀v,Submodule ℝ (Film₁ v))
  (freshHome:Passport (R.family.side m per) V)
  (old:Finset V) (zA:∀v,0∈Actor v) (jointRad:V → ℝ)
local notation "joint" => passport (owner (D.coarser ratio) freshHome old)
local notation "initial" => WilsonMixedReceivedLamp.regular (P:=D.coarser ratio) (Q:=freshHome) (W:=H m) Actor freshA old zA beforeRows
local notation "wage" => (H m).p.supportExponent+1+1
variable {ι₁:Type} [Countable ι₁]
  (birth:Lamps (Affinity.Wallet (actors Actor freshA)) ι₁ G (H m).p
    (passport (owner (D.coarser (Pane.panel R.alloy m (R.alloy.B.a.S.oneStep m per).exact_size).ratio) freshHome old)).origin ρ)

include simple pass education hospital load rank start before phase full course positive y
theorem original (extra:ℝ) (wallet:b ≤ Ω⁻¹)
    (notes:Scene.Armada M w T (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J (m+1))) b order op.count v)
    (seed:Burn.Seed (H (m+1)) (WheelP.M0 epoch.vac 0 (R.alloy.B.a.budget (m+1)) card.extra (H (m+1)).beta))
    (quiet:Burn.Candor (R.alloy.B.a.budget (m+1)) (H (m+1)).activities (Set.range seed.model) (Burn.silver β₁) δ)
    (tuition:input.old.Paid w (H (m+1)).p.B (H (m+1)).p.supportExponent e)
    (forced:input.hard.Paid w (H (m+1)).p.B (H (m+1)).p.supportExponent 1)
    (school:Tableau pieces Actor M) (enrolled:Affinity.Taut D.support Actor pieces input.old)
    (eligible:Affinity.Crown D.support Actor pieces input.hard)
    (positiveJoint:∀v,0<jointRad v) (fits:∀v∈old,jointRad v ≤ w v)
    {regular gross:ℝ} (salary:birth.Paid jointRad (H m).p.B wage regular)
    (all:WilsonRootedKioskOccupiedSlip.Gross birth jointRad (H m).p.B ((H m).p.supportExponent+1) gross)
    (freshTest:Affinity.Taut (joint).support (actors Actor freshA) (WilsonMixedTestTableau.pieces pieces freshK) birth) :
    WilsonOriginalBornLedger.priced (H m) joint ρ (actors Actor freshA) (WilsonMixedTestTableau.pieces pieces freshK)
      birth initial jointRad (Stoop.radius jointRad (WilsonRootedKioskFreeRadius.radius extra slip gross slack))
      residue frozen (fun t' => (Pane.panel R.alloy m u).push (H (m+1)).beta ((Tint.Patrol.picture M input).density
        (left Actor freshA old zA t'))) ∧
    Scene.Armada filedRows w T (E).afterwards ((E).produce (ratio).count*b) order op.count v ∧
    Tableau pieces Actor filedRows ∧ residue ≤ 8*Ω*(e+δ+income) ∧
    WilsonRootedKioskFreeRadius.radius extra slip gross slack ≤ max (max 1 extra) (Ω^5+gross/slack) := by
  let Yh := (intake).2.2.choose
  let uV := (intake).2.2.choose_spec.2.some
  have lower : ∀ U,(H m).eval U≠0 := fun U=>
    (congr_fun (atCoarse).view U).symm ▸ (YM.Multi.AxisShift.chosen_positive R.makes.wilson before.le U).ne'
  have upperBand:(H (m+1)).beta ∈ Shoot.band R.alloy.B.a (m+1) := by
    rw [(atFine).beta]
    exact (R.makes.wilson.represents N per (m+1) before).band
  have realQuiet:Burn.Candor (H (m+1)).p (H (m+1)).activities (Set.range seed.model) (Burn.silver β₁) δ:=by
    rw [(atFine).truep.point]
    exact quiet
  obtain ⟨f,remaining⟩:=Tint.Campus.Hearth.cure (H (m+1)) (Set.range seed.model) _ _ realQuiet
  have capacity:=WheelP.capacitor root table R.alloy R.kit pass epoch.paid
  have bound:δ ≤ incomingE G (R.rolls.L (J (m+1))) β₀:=by
    rw [Push.PriceCompiler.beta_eq R.alloy.B.valid m]
    exact capacity.paid.2
  have taken:=Mentor.Cruise.Semester.on_wallet («R»:=root) («D»:=R.rolls) («Q»:=table)
    («A»:=R.alloy) («F»:=R.kit) (φ:=ψ) («K0»:=books) («h»:=pass) («hE»:=education)
    («r»:=op) («K»:=epoch) («u»:=u) («Actor»:=Actor) («uK»:=pieces) («M»:=M) («w»:=w) («T»:=T) («n₀»:=order) («Vv»:=voter)
    («X'»:=card) («hX»:=journey) («Qa»:=forecast) («hF»:=(atFine).truep.point)
    («hU₁»:=(atFine).truep.path.trans (congr_fun (congr_fun R.alloy.B.bases N) (m+1)))
    («Y'»:=input) («hw»:=positive) («hq»:=(intake).1) («y»:=y) («Yh»:=Yh) («Zj»:=seed)
    («hk»:=(atCoarse).truep.point) («hc»:=hospital) («hs»:=load) (κr:=v) («hκr»:=rank)
    («hβ'»:=upperBand) («hm'»:=before) («g»:=simple) («n»:=per) («hcZ»:=rfl)
    («b'»:=b) («U₀»:=notes) («hvW»:=wallet) («hr»:=phase) («hr'»:=full) («uV»:=uV)
    («hY»:=lower) («hp»:=(course.1.visit m start before).ident) («hO»:=tuition) («hK»:=forced)
    («hδ»:=⟨f,remaining,bound⟩) freshA freshK freshHome old zA jointRad birth extra school enrolled eligible positiveJoint fits salary all freshTest
  exact taken
end YM.Integration.WilsonOriginalSignedWalletCourse
