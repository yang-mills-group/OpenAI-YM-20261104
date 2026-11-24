import YM.Integration.WilsonRootedTwoDateHardPurchase
import YM.Integration.WilsonRootedPhysicalSpringGaussian
import YM.Integration.WilsonRootedTwoDateAmbientGallery
import YM.Integration.WilsonRootedTwoDateIndependentHard

/-! The funded old point comparison and independently tested complete fresh hard insertion on its physical band. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardCourse
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence WilsonRootedTwoDateProduct OPE.Therm
open WilsonLimitConstruction Push.AbsoluteSums.Animals RG.Shoot Pert.Asymptotics
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
local notation "Y" => R.family.path.rep N p (m+1)
local notation "Γ" => Stock.census V
local notation "step" => R.family.path.levels.clock.op (m+1) p
local notation "oneW" => fun _ : V=>(1:ℝ)
variable (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)

local notation "tests" => (ActualOriginalQPointSetup.request R old.labels old.request).tests

/-- The selected physical campaign pays the whole hard correction before either test or gauge field. -/
theorem purchased {ε γ : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {J : Request V}
    {extra : Stage → ℕ → ℝ} {order : ℕ → ℕ → ℕ} {scalar : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit}
    (book : WilsonRootedPhysicalSpringGaussian.Receipt.{u} hG ε J extra γ order R T W scalar)
    (cap : J.inputSupport≤100) (u v : V→MS.Rake.Label B) (prev now q : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v → fresh.request=J →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      WilsonRootedTwoDateHardPurchase.Bought old fresh hG prev ∧
      ∀ x : IndependentTests (ActualOriginalQPointSetup.request R old.labels old.request).tests,
        Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U)) (scene R.family.path N p (m+1)) ∧
        ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U) ∂scene R.family.path N p (m+1) ≤ η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedTwoDatePhysicalHard.original hG book.original book.spring book.marker u v prev now q positive,
    WilsonRootedTwoDateHardHeadroom.selected hG book.spring book.orders J cap,
    WilsonRetainedPaidCourse.selected_norm book.spring book.orders J cap] with m actual solvent feasible
  intro N p old fresh oldu freshv request layout
  obtain ⟨_,hard,bound⟩ := actual N p old fresh oldu freshv layout
  subst J
  obtain ⟨bank,room⟩ := solvent N p fresh.below fresh.schedule
  exact ⟨WilsonRootedTwoDateHardPurchase.at_step old fresh hG prev hard (feasible N p fresh.below fresh.schedule) bank room,bound⟩

end YM.Integration.WilsonRootedTwoDateHardCourse
