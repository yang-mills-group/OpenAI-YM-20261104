import YM.Integration.WilsonLimitConstruction.FundedWilsonStartupGrade
import YM.Integration.NativeWilsonGeneratorAgreement
import YM.Integration.WilsonLimitConstruction.FundedMatchedPointOpening

/-! At the bare Wilson entrance the charged startup action and the complete
microscopic Wilson action give the same filed tensor through the booked order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonInitialPrescribedVacuum
open Function Filter Lattice Wilson Precision RG Source Labels Tree Exterior Marker Multi
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep Comparison.RG02 Comparison.RG02.Bulk
open WilsonLimitConstruction
open scoped Classical

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (camp : Campaign R) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V → ℕ)
    (profile : ∀ k, k ≤ (R.metals.p.profile k).order ∧ k ≤ (R.metals.p.profile k).power)
    (hm : ActualOriginalQInitialInput.start R hG u J A profile ≤ d.level)
    (hp : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val)

local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "F₀" => ActualOriginalQInitialInput.input R hG u J A d Q o μ orders profile hm hp
local notation "W" => FundedMatchedPointOpening.colors R hG u J A d Q o μ orders profile hm hp
local notation "K" => (RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
local notation "S" => R.family.path.levels.clock.op d.level d.period

include camp

theorem original (t : TestSpace (J₀).tests) (F : Forest (S).ratio) (tag : (S).Choices)
    (a : fieldDir G (R.family.side d.level d.period) 1) {r : ℕ} (hr : r ≤ (J₀).order) :
    Bulk.Fk K F tag (W t) a r = Bulk.Fk K F tag ((F₀).colors t) a r := by
  have hjet : Assembly.GradeAt ((J₀).order+3) (Bulk.projected
      (fun g U => (W t).vac g U - ((F₀).colors t).vac g U)) :=
    FundedWilsonStartupGrade.purchase R camp (d.level+1) d.period (J₀).order (J₀).order_ge_two
      ((A₀).inputNorm d.level) ((A₀).inputWidth d.level)
  apply NativeWilsonGeneratorAgreement.of_grade K F tag (W t) ((F₀).colors t).vac a r
    (FundedMatchedPointOpening.well R hG u J A d Q o μ orders profile hm hp t)
    ((F₀).convention.well t)
  exact ⟨hjet.smooth,fun i hi => hjet.vanish i (by omega)⟩

end YM.Integration.WilsonInitialPrescribedVacuum
