import YM.Integration.WilsonOriginalCollarCensusSeats

/-! The teacher on the elected roots has its own inverse-width and support tariff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarWidthReceipt
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




/-- Price the actual Agenda width on the selected roots after fixing the sheet. -/
def charge (request : Request G) (simple : G.Simple) (φ : ℕ → ℕ) (s : Sheet G) (p : MapPrices) (k x : ℕ) : ℝ :=
  let D := WilsonOlderFreshGraphSchool.roots (menu request) simple s p
  let σ := Poetry.Agenda.seed D φ k x
  max (Real.exp (σ⁻¹^2)) (204*σ⁻¹)

def Bill (request : Request G) (simple : G.Simple) (φ : ℕ → ℕ) : Prediction G := fun {M} {_} {A} _ =>
  NativeDiagonalClockRequest.PaidRequests (charge request simple φ M.p M.K) A.B.a

theorem buy (request : Request G) (simple : G.Simple) (φ : ℕ → ℕ) :
    AllPrices (@Bill G request simple φ) := by
  intro s price targets expenses flags programmes wages baton
  refine ⟨0,?_⟩
  intro l _ D w u Z postQ scouts pocket θ steps P menu V quarter
  let charges := charge request simple φ (ThroughLaunch.raise s l) (ThroughLaunch.raging s price)
  obtain ⟨X,more,filed⟩ := NativeDiagonalClockRequest.eventuallyPaid (G:=G) charges _ D θ V
  refine ⟨X,more,?_⟩
  intro Y hY runner wait bill B archive origins rank
  dsimp only
  intro η q exchange aux quote booth sheltered works divides
  exact filed Y hY runner wait B.a B.valid

def Open (request : Request G) (simple : G.Simple) (φ : ℕ → ℕ) (R : Run G) : Prop :=
  let D := WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
  let A := R.family.path.levels
  ∀ k, ∀ᶠ i : ℕ in atTop, ∀ x, x ≤ A.clock.J (i+1) →
    let σ := Poetry.Agenda.seed D φ k x
    let H := A.clock.hatBeta (i+1)
    0 < σ ∧ Real.exp (σ⁻¹^2) ≤ H ∧
      (102:ℝ)/(Nat.ceil ((Real.log H)^2):ℝ) ≤ σ/2

theorem opened (request : Request G) (simple : G.Simple) (φ : ℕ → ℕ) (R : Run G)
    (bill : Bill request simple φ R.kit) : Open request simple φ R := by
  let A := R.family.path.levels
  let D := WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
  have rise : Tendsto A.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  obtain ⟨stage,large⟩ := eventually_atTop.mp (rise.eventually_ge_atTop (Real.exp 2))
  intro k
  obtain ⟨paid,cash⟩ := bill.2 k
  filter_upwards [eventually_ge_atTop stage,eventually_ge_atTop paid] with i late ready
  intro x enrolled
  let σ := Poetry.Agenda.seed D φ k x
  let H := A.clock.hatBeta (i+1)
  have σpos : 0 < σ := by
    unfold σ Poetry.Agenda.seed
    exact div_pos (lt_min (Poetry.Agenda.belt_p D _ _) (Poetry.Agenda.belt_p D _ _)) (by positivity)
  have big : Real.exp 2 ≤ H := large (i+1) (by omega)
  have Hpos : 0 < H := (Real.exp_pos _).trans_le big
  have logbig : 2 ≤ Real.log H := (Real.le_log_iff_exp_le Hpos).2 big
  have fee := cash (i+1) (by omega) x (enrolled.trans (A.fits.mono (Nat.le_succ _)))
  change |max (Real.exp (σ⁻¹^2)) (204*σ⁻¹)| ≤ 1+Real.log (Real.log H) at fee
  have hlog : 1+Real.log (Real.log H) ≤ Real.log H := by
    linarith [Real.log_le_sub_one_of_pos (x:=Real.log H) (by linarith)]
  have bound := (le_abs_self _).trans (fee.trans hlog)
  have Hcost := (le_max_left _ _).trans bound
  have thick : 204*σ⁻¹ ≤ (Nat.ceil ((Real.log H)^2):ℝ) :=
    (le_max_right _ _).trans (bound.trans ((by nlinarith : Real.log H ≤ (Real.log H)^2).trans (Nat.le_ceil _)))
  have cells : (0:ℝ) < (Nat.ceil ((Real.log H)^2):ℝ) :=
    (by nlinarith : (0:ℝ) < (Real.log H)^2).trans_le (Nat.le_ceil _)
  refine ⟨σpos,Hcost.trans (by linarith [Real.log_le_sub_one_of_pos Hpos]),(div_le_iff₀ cells).2 ?_⟩
  have allow := mul_le_mul_of_nonneg_right thick σpos.le
  rw [mul_assoc,inv_mul_cancel₀ σpos.ne',mul_one] at allow
  nlinarith

theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted C s (ThroughLaunch.raging s q))
    (request : WilsonOriginalCollarTeacher.Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ)
    (tube : Comparison.Density.Transport.LinkTube G)
    (extra : Prediction G) (fund : AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      Open request simple φ R ∧
      (∀ k (S : Syl.School k), 2 ≤ S.order → ∀ᶠ m in atTop, WilsonOriginalCollarCensusSeats.Dated request simple R S m) ∧
      WilsonOriginalCollarPhysicalBooks.Gates request simple R ∧ Covered (WilsonEmittedDictionary.program tube) R ∧
      House request simple C R ∧ WilsonOriginalCollarFiledRealm.Filed request R ∧ Neutral request R.kit ∧
      extra R.kit ∧ OnRun.{u} cap simple ε C U (@WilsonOriginalSeparatedElection.demands G φ simple C split U bills
        (Together (@WilsonOriginalSmallStrip.Filed G (WilsonOriginalSeparatedCalendar.calendar additional))
          (@requests G φ request simple C split
            (Together (@WilsonOriginalCollarPhysicalBooks.PatchBill G (WilsonEmittedDictionary.program tube)) (Together (@Bill G request simple φ) (@extra)))))) R T W ∧
      WilsonOriginalSeparatedCalendar.Capped simple C R ∧ WilsonOriginalSeparatedCalendar.Open additional R ∧
      WilsonPositionProgramNestedElection.course simple a OPE.Stroke.epsilonR R.kit ∧
      R2I.RG05Joint.AcrossPanels R.kit ∧ (∀ i, (R.family.path.levels.budget i).supportExponent=100) ∧
      WilsonOriginalSeparatedElection.Quiet R ∧ ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        WilsonMacroscopicFundedReader.Elected.{u} R simple cohort := by
  obtain ⟨R,T,W,seats,gates,covered,house,original,neutral,fees,rest⟩ :=
    WilsonOriginalCollarCensusSeats.original.{u} a cap U mono simple positive C split permitted
      request additional bills tube (Together (@Bill G request simple φ) (@extra))
      (fun s q => joint (buy request simple φ s q) (fund s q))
  exact ⟨R,T,W,opened request simple φ R fees.1,seats,gates,covered,house,original,neutral,fees.2,rest⟩

/-- The physical aperture and the reporting subsidy both have original issuers. -/
abbrev physical (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (request : Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ) :=
  original.{u} a cap U mono simple positive (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits)
    le_rfl (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
    request additional bills (Classical.choice (Comparison.Density.Transport.tube_exists G))
    (@WilsonReportColumnSubsidy.Eligible G) WilsonReportColumnSubsidy.allPrices

end YM.Integration.WilsonOriginalCollarWidthReceipt
end
