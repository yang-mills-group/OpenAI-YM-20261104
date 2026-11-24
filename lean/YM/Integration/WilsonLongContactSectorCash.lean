import YM.Integration.WilsonLongContactRebudget
import YM.Integration.ActualRunFixedOrders
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! The incumbent fine field, its complete restricted intake and the funded sector score
on a single actual booked tube. The date threshold precedes every period and cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactSectorCash
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
open Extra.Iteration.Comparison WilsonLongContactRebudget
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] (J : Request V)
    (Δ : Daisy.Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ) (R : Run G)
    (paid : QLocalRequestedSectorCalendar.Paid J Δ extra γ R.kit) (A : NumericSchedule R.family J)
    {Γ : Census V} (z : LocalFormal.Datum R.family Γ)
local notation "a₀" => R.alloy.B.a
local notation "j₁" => R.alloy.B.a.clock.J (z.level+1)
local notation "j₀" => R.alloy.B.a.clock.J z.level
local notation "T₀" => ships R.alloy.B z.cutoff z.level z.period
local notation "b₀" => paid.choose (j₁) (j₀)
local notation "C₀" => libretto J R.metals.p R.metals.K (j₁) (j₀)
local notation "P₀" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "win₀" => QLocalRequestedSectorCalendar.selected J Δ extra γ R paid z

structure Issued : Prop where
  budget : HasBudget (Y₁).p (A.inputNorm z.level)
  original : OriginalMarkedPhysicalCash.Available J (win₀) (T₀) (Y₁)
  restricted : OriginalMarkedPhysicalCash.Available J (win₀) (T₀) (atBudget (Y₁) (A.inputNorm z.level))
  recorded : Plays (C₀) (b₀).record (A.outputNorm z.level) (A.inputNorm z.level)
    (teller J (P₀)) (T₀) ((a₀).clock.hatBeta z.level)

theorem purchased (orders : ∀i,i≤(R.metals.p.profile i).order ∧ i≤(R.metals.p.profile i).power)
    (contract : J.inputSupport=100) (fixed : ∀i,((a₀).params i).supportExponent = 100) :
    ∀ᶠ m : ℕ in atTop, ∀ {Γ : Census V} (z : LocalFormal.Datum R.family Γ), z.level=m →
      Issued J Δ extra γ R paid A z := by
  filter_upwards [ActualRunFixedOrders.eventually_orders R orders J.inputFieldOrder J.inputDistanceOrder]
    with m enough Γ z hm
  subst m
  let Y := R.family.path.rep z.cutoff z.period (z.level+1)
  have vac : Y.p=R.family.path.levels.budget (z.level+1) :=
    (R.makes.wilson.represents z.cutoff z.period (z.level+1) z.below).vac
  have matchSupport : J.inputSupport=Y.p.supportExponent := by
    rw [vac]
    exact contract.trans (fixed (z.level+1)).symm
  have ask := A.input_norm z.level
  have h : HasBudget Y.p (A.inputNorm z.level) := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · rw [vac,ask.threshold]
    · rw [vac,ask.order]
      exact enough.1
    · rw [vac,ask.distance]
      exact enough.2
    · rw [vac,ask.block]
    · exact (ask.reserve.trans matchSupport).le
  have supply := (R.T.sticks z.cutoff z.period).prices (z.level+1) (Nat.zero_le _) z.below
  have old := Application.intake_at R.alloy.B z.cutoff z.level z.period z.below Y supply.1 supply.2
  have entry := OriginalMarkedPhysicalCash.retell J old matchSupport
  have revised := WilsonLongContactRebudget.intake entry h ask.reserve.symm
  have original := OriginalMarkedPhysicalCash.actual J Δ extra γ R paid z matchSupport
  have stamp := original.choose_spec.2.1
  refine ⟨h,original,?_,(QLocalRequestedSectorCalendar.recording J Δ extra γ R paid A z).1⟩
  apply OriginalMarkedPhysicalCash.window J
    (QLocalRequestedSectorCalendar.selected J Δ extra γ R paid z) _ _ _ stamp revised
  exact ⟨revised.ready,rfl,by rw [add_comm 1]; exact R.alloy.B.a.fits.sizeT _ _⟩

theorem funded {hG : G.Simple} {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (fund : FundedOriginalProperties hG ε W)
    (orders : ∀i,i≤(R.metals.p.profile i).order ∧ i≤(R.metals.p.profile i).power)
    (contract : J.inputSupport=100) :
    ∀ᶠ m : ℕ in atTop, ∀ {Γ : Census V} (z : LocalFormal.Datum R.family Γ), z.level=m →
      Issued J Δ extra γ R paid A z :=
  purchased J Δ extra γ R paid A orders contract fund.2.1.paid.fixed

end YM.Integration.WilsonLongContactSectorCash
