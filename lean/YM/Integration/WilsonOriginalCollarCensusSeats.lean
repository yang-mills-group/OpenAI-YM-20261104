import YM.Integration.WilsonOriginalCollarPhysicalBooks
import YM.Integration.WilsonMeasuredPointHouseSeats

/-! The actual original appointments carry the chosen lessons and the full hard gates on one roster. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarCensusSeats
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



/-- All opportunities and hard receipts on the same appointment, before choosing its period. -/
def Dated (request : Request G) (simple : G.Simple) (R : Run G) {k : ℕ} (S : Syl.School k) (m : ℕ) : Prop :=
  let menu := WilsonOriginalCollarTeacher.menu request
  let D := WilsonOlderFreshGraphSchool.roots menu simple R.metals.p R.metals.K
  let Q := WilsonOlderFreshGraphSchool.rollTab menu simple R.metals R.rolls
  ∀ N, m ≤ N → ∃ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (lessons : ∀ i, ∀ (hi : m ≤ i), i < N → Oak.Lesson (N:=N) R hk D Q π Γ hi),
    PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ ∧
    ∀ per, ∃ Ψ : (i : ℕ) → RG.Rep G (R.family.side i per),
      Concourse R.alloy R.kit R.T π Γ m N per k Ψ ∧
      Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
      (∀ i (lo : m ≤ i) (live : i < N),
        Nonempty (Oak.Calendar R hk D Q π Γ Ψ lo (N:=N) (lessons i lo live)) ∧
        ∃ op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i),
          op.count=S.pieces ∧ op.stage=S.order+1) ∧
      ∀ i, m ≤ i → i ≤ N → ∀ q ell load, q+ell*load ≤ R.alloy.B.a.clock.J i →
        ∃ f, Topline (Ψ i) f ∧ ((R.alloy.B.a.clock.hatBeta i)^ell)^load * f ≤
          (R.alloy.B.a.clock.hatBeta i)^(-(q:ℝ)) * forcedDivisor R.family i

theorem on_house (request : Request G) (simple : G.Simple) (C : VowsR.LawScroll G φ) (R : Run G)
    (house : House request simple C R) (way : WayStation R.kit) (k : ℕ) (S : Syl.School k)
    (deep : 2 ≤ S.order) : ∀ᶠ m in atTop, Dated request simple R S m := by
  let menu := WilsonOriginalCollarTeacher.menu request
  let D := WilsonOlderFreshGraphSchool.roots menu simple R.metals.p R.metals.K
  let Q := WilsonOlderFreshGraphSchool.rollTab menu simple R.metals R.rolls
  obtain ⟨books,forecast,physical,_,_,_,_,_,ticket,_⟩ := house
  have appointments := WilsonMeasuredPointHouseSeats.original R D Q C books forecast physical S deep
  filter_upwards [appointments] with m issued
  intro N band
  obtain ⟨π,Γ,hk,lessons,layout,boards⟩ := issued N band
  refine ⟨π,Γ,hk,lessons,layout,fun per => ?_⟩
  obtain ⟨Ψ,course,top,calendars⟩ := boards per
  refine ⟨Ψ,course,top,calendars,?_⟩
  intro i lo hi q ell load admitted
  exact WilsonMovingMentorStartingHard.throughout R way D Q π Γ Ψ course ticket
    lo q ell load hi admitted top

theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted C s (ThroughLaunch.raging s q))
    (request : WilsonOriginalCollarTeacher.Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ)
    (tube : Comparison.Density.Transport.LinkTube G)
    (extra : Prediction G) (fund : AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∀ k (S : Syl.School k), 2 ≤ S.order → ∀ᶠ m in atTop, Dated request simple R S m) ∧
      WilsonOriginalCollarPhysicalBooks.Gates request simple R ∧ Covered (WilsonEmittedDictionary.program tube) R ∧
      House request simple C R ∧ WilsonOriginalCollarFiledRealm.Filed request R ∧ Neutral request R.kit ∧
      extra R.kit ∧ OnRun.{u} cap simple ε C U (@WilsonOriginalSeparatedElection.demands G φ simple C split U bills
        (Together (@WilsonOriginalSmallStrip.Filed G (WilsonOriginalSeparatedCalendar.calendar additional))
          (@requests G φ request simple C split
            (Together (@WilsonOriginalCollarPhysicalBooks.PatchBill G (WilsonEmittedDictionary.program tube)) (@extra))))) R T W ∧
      WilsonOriginalSeparatedCalendar.Capped simple C R ∧ WilsonOriginalSeparatedCalendar.Open additional R ∧
      WilsonPositionProgramNestedElection.course simple a OPE.Stroke.epsilonR R.kit ∧
      R2I.RG05Joint.AcrossPanels R.kit ∧ (∀ i, (R.family.path.levels.budget i).supportExponent=100) ∧
      WilsonOriginalSeparatedElection.Quiet R ∧ ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        WilsonMacroscopicFundedReader.Elected.{u} R simple cohort := by
  obtain ⟨R,T,W,gates,covered,house,rest⟩ := WilsonOriginalCollarPhysicalBooks.original.{u}
    a cap U mono simple positive C split permitted request additional bills tube (@extra) fund
  exact ⟨R,T,W,on_house request simple C R house gates.1,gates,covered,house,rest⟩

/-- The physical aperture and the reporting subsidy both have original issuers. -/
abbrev physical (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (request : Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ) :=
  original.{u} a cap U mono simple positive (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits)
    le_rfl (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
    request additional bills (Classical.choice (Comparison.Density.Transport.tube_exists G))
    (@WilsonReportColumnSubsidy.Eligible G) WilsonReportColumnSubsidy.allPrices

end YM.Integration.WilsonOriginalCollarCensusSeats
end
