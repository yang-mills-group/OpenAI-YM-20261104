import YM.Integration.WilsonOriginalCollarElection
import YM.Integration.WilsonEmittedOriginalCalendar
import YM.Integration.WilsonMatrixTicketLanesVacuumMentor

/-! Physical all-period prices and exact compulsory stocks on the same capped course. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarPhysicalBooks
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowCompany WilsonFundedWindowMenu WilsonWindowJointPurchase WilsonWindowBookPurchase
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open LocalComparison
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {φ : ℕ → ℕ}


/-- Declare the full profile tariff after the purchased lengths and before
the cutoff and physical period. All profile parameters are the selected ones. -/
def PatchBill (C : Cost) : Prediction G := fun {M} {_} {A} _ =>
  ∃ (s : Sheet G) (n : ℕ → ℕ), M.p = ThroughLaunch.raise s n ∧
    NativeDiagonalClockRequest.PaidRequests (post C s (fun i => (A.B.a.clock.factor i).val)) A.B.a

theorem buy_patch (C : Cost) : AllPrices (@PatchBill G C) := by
  intro s price targets expenses flags programmes wages baton
  refine ⟨0,?_⟩
  intro l _ D w u Z postQ scouts pocket θ steps P menu V quarter
  let charges := post C s (fun i => (D.L i).val)
  obtain ⟨X,more,filed⟩ := NativeDiagonalClockRequest.eventuallyPaid (G:=G) charges _ D θ V
  refine ⟨X,more,?_⟩
  intro Y hY runner wait bill B archive origins rank
  dsimp only
  intro η q exchange aux quote booth sheltered works divides
  refine ⟨s,l,rfl,?_⟩
  simpa only [charges,B.valid.lengths] using filed Y hY runner wait B.a B.valid

theorem actual_patch (R : Run G) (simple : G.Simple) (C : Cost) (bill : PatchBill C R.kit) :
    Covered C R := by
  obtain ⟨s,l,same,cash⟩ := bill
  exact FundedDictionaryPatchPrices.covered C R simple s l same cash

/-- The two-received stock at the original dates is attached to this capped gallery. -/
def Gates (request : Request G) (simple : G.Simple) (R : Run G) : Prop :=
  let menu := WilsonOriginalCollarTeacher.menu request
  let r := WilsonOlderFreshGraphSchool.roots menu simple R.metals.p R.metals.K
  let seat := WilsonOlderFreshGraphSchool.rollTab menu simple R.metals R.rolls
  WayStation R.kit ∧ WilsonMovingMentorWarm.Conditions R.kit ∧
    ∀ k m N : ℕ, Burn.horizon k + 2 ≤ R.alloy.B.a.clock.J m → m ≤ N →
    ∃ π Γ, PlanV.Path r R.alloy seat (Burn.horizon k) N m π Γ ∧
    ∀ per, ∃ H : (i : ℕ) → RG.Rep G (R.family.side i per),
      Concourse R.alloy R.kit R.T π Γ m N per k H ∧
      Topline (H N) (R.family.path.levels.clock.forcedAllowance N) ∧
      ∀ i, m ≤ i → i ≤ N →
        (H i).beta = (R.family.path.rep N per i).beta ∧ (H i).eval = (R.family.path.rep N per i).eval ∧
        ∀ q ell load : ℕ, q + ell * load ≤ R.alloy.B.a.clock.J i →
          ∃ f, Topline (H i) f ∧
            ((R.alloy.B.a.clock.hatBeta i)^ell)^load * f ≤
              (R.alloy.B.a.clock.hatBeta i)^(-(q:ℝ)) * forcedDivisor R.family i


theorem original_gates (R : Run G) (simple : G.Simple) (request : Request G)
    (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (purchased : WilsonOlderFreshGraphSchool.grant (menu request) simple (law C split) R.kit) :
    Gates request simple R := by
  let r := WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
  let seat := WilsonOlderFreshGraphSchool.rollTab (menu request) simple R.metals R.rolls
  obtain ⟨_,frost,passport,_⟩ := purchased.1
  have ticket : TicketP R.alloy R.kit r seat := purchased.2
  have warm : WilsonMovingMentorWarm.Conditions R.kit := ⟨⟨ticket.head',frost⟩,passport⟩
  have way : WayStation R.kit := ⟨⟨r,seat,ticket⟩,frost,passport⟩
  refine ⟨way,warm,?_⟩
  intro k m N rank live
  obtain ⟨π,Γ,layout,issued⟩ := WilsonMovingMentorTerrace.original R simple warm ticket.pledge rank live
  refine ⟨π,Γ,layout,fun per => ?_⟩
  obtain ⟨H,story,top,paid⟩ := issued per
  refine ⟨H,story,top,?_⟩
  intro i first reached
  refine ⟨(paid i first reached).1,(paid i first reached).2.1,?_⟩
  intro q ell load attained
  exact WilsonMovingMentorStartingHard.throughout R way r seat π Γ H story ticket
    first q ell load reached attained top


theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted C s (ThroughLaunch.raging s q))
    (request : WilsonOriginalCollarTeacher.Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ)
    (tube : Comparison.Density.Transport.LinkTube G)
    (extra : Prediction G) (fund : AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      Gates request simple R ∧ Covered (WilsonEmittedDictionary.program tube) R ∧
      House request simple C R ∧ WilsonOriginalCollarFiledRealm.Filed request R ∧ Neutral request R.kit ∧
      extra R.kit ∧ OnRun.{u} cap simple ε C U (@WilsonOriginalSeparatedElection.demands G φ simple C split U bills
        (Together (@WilsonOriginalSmallStrip.Filed G (WilsonOriginalSeparatedCalendar.calendar additional))
          (@requests G φ request simple C split
            (Together (@PatchBill G (WilsonEmittedDictionary.program tube)) (@extra))))) R T W ∧
      WilsonOriginalSeparatedCalendar.Capped simple C R ∧ WilsonOriginalSeparatedCalendar.Open additional R ∧
      WilsonPositionProgramNestedElection.course simple a OPE.Stroke.epsilonR R.kit ∧
      R2I.RG05Joint.AcrossPanels R.kit ∧ (∀ i, (R.family.path.levels.budget i).supportExponent=100) ∧
      WilsonOriginalSeparatedElection.Quiet R ∧ ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        WilsonMacroscopicFundedReader.Elected.{u} R simple cohort := by
  let tariff := WilsonEmittedDictionary.program tube
  obtain ⟨R,T,W,house,realm,neutral,tariffs,school,prior,strips,nested,panels,alpha,quiet,geometry⟩ :=
    WilsonOriginalCollarElection.original.{u} a cap U mono simple positive C split permitted
      request additional bills (Together (@PatchBill G tariff) (@extra))
      (fun s q => joint (buy_patch tariff s q) (fund s q))
  have sale := school.2.1.2.2.2.2
  exact ⟨R,T,W,original_gates R simple request C split sale.1,actual_patch R simple tariff tariffs.1,
    house,realm,neutral,tariffs.2,school,prior,strips,nested,panels,alpha,quiet,geometry⟩

/-- The physical aperture and the reporting subsidy both have original issuers. -/
abbrev physical (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (request : Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ) :=
  original.{u} a cap U mono simple positive (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits)
    le_rfl (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
    request additional bills (Classical.choice (Comparison.Density.Transport.tube_exists G))
    (@WilsonReportColumnSubsidy.Eligible G) WilsonReportColumnSubsidy.allPrices

end YM.Integration.WilsonOriginalCollarPhysicalBooks
end
