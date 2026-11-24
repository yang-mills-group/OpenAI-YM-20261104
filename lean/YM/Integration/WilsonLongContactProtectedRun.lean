import YM.Integration.WilsonLongContactSectorProtection
import YM.Integration.WilsonLongContactSectorSeat
import YM.Integration.WilsonMovingRenderedElection

/-! The same presold record, tagged Cash, true angular chart, and after-length numerical
forecast in the moving original physical campaign. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactProtectedRun
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale
open Extra.Iteration.Comparison WilsonLongContactRebudget WilsonLongContactSectorProtection
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} (J : Request V)

/-- The signed forecast is compared at the actual temperature, after the block and
the entire booking have been fixed. -/
abbrev Forecast (G : Gauge) (n : ℕ) :=
  ∀ {P : Teller G}, ConnectedActivityE6.Target G P → Patch → Libretto G n → Booking G → ℝ → ℝ → Prop

def charge (φ : Forecast G J.outputFieldOrder) (v : ℝ) : Premium G J.outputFieldOrder :=
  fun Q D C b x => ∃ k : ℝ, |k| ≤ betaF G x D.L ^ v ∧ φ Q D C b x k

theorem tariff (φ : Forecast G J.outputFieldOrder) (v : ℝ) (hv : -(1/2:ℝ)<v)
    (supplier : ∀ {P : Teller G} (Q : ConnectedActivityE6.Target G P)
      (D : Patch) (C : Libretto G J.outputFieldOrder) (b : Booking G), D.Branches P.bind G →
      b.record.ε ≤ 1/4 → ∃ k : ℝ → ℝ, Rate G D.L (-(1/2:ℝ)) k ∧ ∀ᶠ x : ℝ in atTop, φ Q D C b x (k x)) :
    Admitted J (charge J φ v) := by
  intro P Q D C b branch cap
  obtain ⟨k,rate,field⟩ := supplier Q D C b branch cap
  filter_upwards [rate v hv,field] with x hx hc
  exact ⟨k x,hx,hc⟩

variable (Δ : Daisy.Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ) (R : Run G)
    (ρ : Premium G J.outputFieldOrder)
    (paid : WilsonLongContactSectorProtection.Paid J Δ extra γ ρ R.kit)

include paid in
theorem inherited : QLocalRequestedSectorCalendar.Paid J Δ extra γ R.kit := by
  obtain ⟨b,hbe,win⟩ := paid
  refine ⟨b,hbe,?_⟩
  intro j x hx i st fr
  have e := win j x hx i st fr
  exact ⟨e.1.window,e.2⟩

variable [DecidableEq V] (A : NumericSchedule R.family J) {Γ : Census V} (z : LocalFormal.Datum R.family Γ)
local notation "j₁" => R.alloy.B.a.clock.J (z.level+1)
local notation "j₀" => R.alloy.B.a.clock.J z.level
local notation "T₀" => ships R.alloy.B z.cutoff z.level z.period
local notation "S₀" => R.alloy.B.a.clock.op z.level z.period
local notation "x₀" => R.alloy.B.a.clock.hatBeta z.level
local notation "b₀" => paid.choose (j₁) (j₀)
local notation "C₀" => libretto J R.metals.p R.metals.K (j₁) (j₀)
local notation "Q₀" => R.kit.target (j₁) (j₀)
local notation "P₀" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)

theorem reported : Offered J ρ Δ (Q₀) (C₀) (b₀) (S₀).patch (x₀) γ ∧
    Earlier J R.metals.p R.metals.K extra (j₁) (j₀) (S₀).patch.L.val := by
  have st := step_paid R.alloy.B.a z.level
  have fr := first_le R.alloy.B.valid z.level
  have hL : (S₀).patch.L=R.rolls.L (j₁) := block_eq R.alloy.B.valid _
  have hJ : (S₀).patch.J=(j₁) := (Testing.proceeds R.alloy.B z.cutoff z.level z.period z.below).atStep
  have hP : (S₀).patch=Clockwork.patch R.rolls st fr := by
    cases he : (S₀).patch
    rw [he] at hL hJ
    unfold Clockwork.patch
    congr
  constructor
  · rw [hP]
    exact (paid.choose_spec.2 _ _ (R.alloy.B.valid.pays _) _ st fr).1
  · rw [hL]
    exact paid.choose_spec.1 _ _ st

structure Field : Prop where
  reserve : (b₀).record.ε≤1/4
  forecast : ρ (target J (Q₀)) (S₀).patch (C₀) (b₀) (x₀)
  budget : HasBudget (Y₁).p (A.inputNorm z.level)
  cash : OriginalMarkedPhysicalCash.Available J
    (reported J Δ extra γ R ρ paid z).1.window (T₀) (atBudget (Y₁) (A.inputNorm z.level))
  plays : Plays (C₀) (b₀).record (A.outputNorm z.level) (A.inputNorm z.level)
    (teller J (P₀)) (T₀) (x₀)

theorem original {hG : G.Simple} {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (fund : FundedOriginalProperties hG ε W)
    (orders : ∀i,i≤(R.metals.p.profile i).order ∧ i≤(R.metals.p.profile i).power)
    (contract : J.inputSupport=100) :
    ∀ᶠ m : ℕ in atTop, ∀ {Γ : Census V} (z : LocalFormal.Datum R.family Γ), z.level=m →
        Field J Δ extra γ R ρ paid A z := by
  let base := inherited J Δ extra γ R ρ paid
  filter_upwards [WilsonLongContactSectorCash.funded J Δ extra γ R base A fund orders contract]
    with m verified Γ z hm
  have e := verified z hm
  have chosen := reported J Δ extra γ R ρ paid z
  let Y := R.family.path.rep z.cutoff z.period (z.level+1)
  have supply := (R.T.sticks z.cutoff z.period).prices (z.level+1) (Nat.zero_le _) z.below
  have old := Application.intake_at R.alloy.B z.cutoff z.level z.period z.below Y supply.1 supply.2
  have vac : Y.p=R.family.path.levels.budget (z.level+1) :=
    (R.makes.wilson.represents z.cutoff z.period (z.level+1) z.below).vac
  have support : J.inputSupport=Y.p.supportExponent := by
    rw [vac]
    exact contract.trans (fund.2.1.paid.fixed (z.level+1)).symm
  have entry := OriginalMarkedPhysicalCash.retell J old support
  have revised := WilsonLongContactRebudget.intake entry e.budget (A.input_norm z.level).reserve.symm
  have win := chosen.1.window
  have hs := PhysicalNext.Repeat.Opera.protocol (n:=z.period) R.alloy.B z.below R.kit.pledging.conducts.full
  refine ⟨chosen.1.small,chosen.1.forecast,e.budget,?_,
    (QLocalRequestedSectorCalendar.record_at J Δ extra γ R A z _ win chosen.2).1⟩
  apply OriginalMarkedPhysicalCash.window J win _ _ _ hs revised
  exact ⟨revised.ready,rfl,by rw [add_comm 1]; exact R.alloy.B.a.fits.sizeT _ _⟩

end YM.Integration.WilsonLongContactProtectedRun
