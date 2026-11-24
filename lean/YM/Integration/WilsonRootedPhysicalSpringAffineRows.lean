import YM.Integration.WilsonRootedPhysicalSpringGaussian
import YM.Integration.ManuscriptQLocalSelectedMeasuredRows
import YM.Integration.ManuscriptQLocalCofinalAffineFields

/-! All finite Gaussian and measured-conditional orders on the original physical spring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalSpringAffineRows

open Function Filter Lattice Wilson RG RG.Shoot RG.Supply Precision Marker Org
open Push.PriceCompiler Push.SectorMeasure Next.SectorChange Gaussian
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open LocalComparison Comparison.RG02 PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Progress.DirectedRecipe WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open ManuscriptQLocalCofinalAffineFields
open scoped Topology Classical
universe u

/-- A single lower stage licenses the requested order on every torus and with every analytic input.
The fixed program includes its actual positive charged-to-quiet conditional and complete field prices. -/
def After {G : Gauge} (R : Run G) (paid : Paid R) (through first : ℕ) : Prop :=
  ∀ {I : Type} [DecidableEq I] {Γ : Census I} (d : LocalFormal.Datum R.family Γ),
    first ≤ d.level → through ≤ R.alloy.B.a.clock.J (d.level+1) ∧ Contracted R d paid through ∧
    ∀ (D : Allocation G (R.family.path.levels.clock.op d.level d.period) (R.alloy.B.a.clock.hatBeta d.level)
        (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)))
      (q : Chi) [Fintype I] {J : Request I} {A : NumericSchedule R.family J}
      (H : AnalyticInput J A d) (x : TestSpace J.tests),
      ManuscriptQLocalSelectedMeasuredRows.At R d D q H x paid

theorem window {G : Gauge} (R : Run G) (paid : Paid R) (through : ℕ) :
    ∃ first : ℕ, After R paid through first := by
  have deep : Tendsto R.alloy.B.a.clock.J atTop atTop := R.family.path.levels.fits.deep
  obtain ⟨first, ready⟩ := eventually_atTop.mp (deep.eventually_ge_atTop through)
  refine ⟨first,?_⟩
  intro I inst Γ d eligible
  have enough := ready (d.level+1) (eligible.trans (Nat.le_succ _))
  refine ⟨enough, row R d paid through enough, ?_⟩
  intro D q fi J A H x
  exact ManuscriptQLocalSelectedMeasuredRows.measuredAt R d D q H x paid

/-- An independently priced receipt can be filed with the same scalar budget before the run is built. -/
theorem purchasedWith {G : Gauge} {V : Type} [Fintype V] (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) (paid : Paid R),
      prediction R.kit ∧ WilsonRootedPhysicalSpringGaussian.Receipt.{u} hG ε J extra γ schedule R T W paid.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      ∀ through : ℕ, ∃ first : ℕ, After R paid through first := by
  let stock := @FundedPredictionSupply.Both G (@ManuscriptQLocalScalarClockPurchase.Paid G schedule) (@prediction)
  obtain ⟨R,T,W,source,booked,physical⟩ :=
    WilsonRootedPhysicalSpringGaussian.selectedWith.{u} hG hε J extra γ hγ schedule (@stock)
      (fun s t => FundedPredictionSupply.both
        (ManuscriptQLocalScalarClockPurchase.prepaid schedule s (ThroughLaunch.raging s t)) (price s t))
  let paid : Paid R := ⟨source, booked.1⟩
  exact ⟨R,T,W,paid,booked.2,physical,ManuscriptQLocalScalarProgramSelection.measuredOn R,window R paid⟩

/-- A genuine original physical spring carries the comparisons to every finite order on the same campaign. -/
theorem purchased {G : Gauge} {V : Type} [Fintype V] (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) (paid : Paid R),
      WilsonRootedPhysicalSpringGaussian.Receipt.{u} hG ε J extra γ schedule R T W paid.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      ∀ through : ℕ, ∃ first : ℕ, After R paid through first := by
  obtain ⟨R,T,W,paid,_,physical,jets,rows⟩ := purchasedWith.{u} hG hε J extra γ hγ
    (@FundedPredictionSupply.Always G) (fun s t => FundedPredictionSupply.always s (ThroughLaunch.raging s t))
  exact ⟨R,T,W,paid,physical,jets,rows⟩

end YM.Integration.WilsonRootedPhysicalSpringAffineRows
end
