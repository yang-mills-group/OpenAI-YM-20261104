import YM.Integration.WilsonThermometerWeakMatrixSchool
import YM.Integration.WilsonPositionProgramNestedElection
import YM.Integration.WilsonPositionProgramStageInvoice
import YM.Integration.WilsonOlderFreshGraphCommonHouse
import YM.Integration.WilsonVacuumPreResetFiniteHeatHierarchy
import YM.Integration.FundedMarkedCoverRows
import YM.Integration.WilsonMacroscopicFundedReader
import YM.Integration.WilsonMatrixTicketFuelLanes

/-! Fund the original classroom, capped graph books, all finite ordered rosters
and the moving physical matrix in a single Wilson election. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedElection
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase WilsonWindowBookPurchase
open WilsonReportingAbsoluteInletSchool MSbar.Heath
open OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonMarkedIndependentPhysicalIntake WilsonVacuumPreResetFiniteHeatScale
open WilsonVacuumPreResetFiniteHeatTable
open scoped Classical
universe u
variable {G : Gauge} {φ : ℕ → ℕ}

/-- Stage j pays the first j+1 named post-length gear bills. -/
def amount (bills : ℕ → ℕ → Gear G → ℝ) (j : ℕ) (g : Gear G) : ℝ :=
  ∑ n ∈ range (j+1), |bills n j g|

theorem funded_bill (bills : ℕ → ℕ → Gear G → ℝ) (j n : ℕ) (live : n ≤ j)
    (g : Gear G) : bills n j g ≤ amount bills j g :=
  (le_abs_self _).trans (Finset.single_le_sum
    (f := fun k => |bills k j g|) (fun _ _ => abs_nonneg _) (mem_range_succ_iff.mpr live))

def cover (bills : ℕ → ℕ → Gear G → ℝ) : Prediction G :=
  Together (@FundedMarkedCoverRows.prices G (WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose)
    (@FundedMarkedCoverRows.prices G (amount bills))

private theorem paid_cover (bills : ℕ → ℕ → Gear G → ℝ) :
    WilsonFundedWindowMenu.AllPrices (@cover G bills) := by
  have grant (v : ℕ → Gear G → ℝ) : WilsonFundedWindowMenu.AllPrices (@FundedMarkedCoverRows.prices G v) :=
    fun s M => WilsonFundedWindowMenu.from_guard
      (WilsonFundedWindowCompany.of_prepaid (FundedMarkedCoverRows.purchase v s M))
  exact fun s M => joint (grant _ s M) (grant _ s M)

/-- All three forecasts are declared before choosing the run. The covered
vacuum and marked prices use the finite menu at its actual stage. -/
def demands (simple : G.Simple) (law : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ) (U : ℕ → ℕ) (bills : ℕ → ℕ → Gear G → ℝ)
    (extra : Prediction G) : Prediction G :=
  Together (@WilsonOlderFreshGraphCommonHouse.supply G φ simple law split U)
    (Together (@cover G bills)
      (Together (@WilsonPositionProgramStageInvoice.Requested G) (@extra)))

theorem prepaid (simple : G.Simple) (law : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted law s (ThroughLaunch.raging s q))
    (U : ℕ → ℕ) (bills : ℕ → ℕ → Gear G → ℝ) (extra : Prediction G)
    (paid : WilsonFundedWindowMenu.AllPrices (@extra)) :
    WilsonFundedWindowMenu.AllPrices (@demands G φ simple law split U bills (@extra)) := fun s q =>
  joint (WilsonOlderFreshGraphCommonHouse.prepaid simple law split U permitted s q)
    (joint (paid_cover bills s q)
      (joint (WilsonPositionProgramStageInvoice.prepaid simple s _) (paid s q)))

def Quiet (R : Run G) : Prop := ∀ e : ℕ, ∀ᶠ m : ℕ in atTop,
  ∃ s B : ℝ, 0 < s ∧ 1 ≤ B ∧ ∀ N p : ℕ, m ≤ N →
    table R.family.path.levels R.metals.O e N m (R.family.side m p) (rate R.family.path.levels m p) ∧
    PositiveAt R.family.path.levels R.metals.O e N m (R.family.side m p) s B

/-- The law, physical axis, requested powers, and any extra permitted invoices
are fixed first. The original extraction and its finite public panels come later. -/
theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap)
    (simple : G.Simple) {ε ξ : ℝ} (positive : 0 < ε) (finance : Glacier (a := a) simple ξ)
    (law : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted law s (ThroughLaunch.raging s q))
    (bills : ℕ → ℕ → Gear G → ℝ) (extra : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      OnRun.{u} cap simple ε law U (@demands G φ simple law split U bills (@extra)) R T W ∧
      WilsonPositionProgramNestedElection.course simple a ξ R.kit ∧ R2I.RG05Joint.AcrossPanels R.kit ∧
      (∀ i, (R.family.path.levels.budget i).supportExponent = 100) ∧ Quiet R ∧
      ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        WilsonMacroscopicFundedReader.Elected.{u} R simple cohort := by
  obtain ⟨V, clear⟩ := MSbar.Heath.vocals G
  obtain ⟨R, T, W, licence, panels, school⟩ := WilsonReportingAbsoluteInletSchool.withMatrixSelected.{u}
    cap mono simple positive (WilsonPositionProgramNestedElection.funded simple finance)
    V clear law split permitted U (@demands G φ simple law split U bills (@extra))
    (prepaid simple law split permitted U bills (@extra) paid)
  have physical : FundedOriginalProperties.{u} simple ε W := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := school
    exact h
  have quiet := (WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose_spec R simple
    physical.2.2.2.2.2.2.1 school.2.1.2.1.1
  exact ⟨R, T, W, school, licence, panels, physical.2.1.paid.fixed, quiet,
    WilsonMacroscopicFundedReader.original.{u} R simple W physical
      (WilsonMatrixTicketFuelPrice.lanes R finance.price finance.charge licence.1)⟩

end YM.Integration.WilsonOriginalSeparatedElection
end

