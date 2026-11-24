import YM.Integration.WilsonRootedTwoDateHardFixed

/-! The secondary hard radius is fixed before the cutoff, period, both tests and gauge configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardPrepaid
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

open RG3.Script.Picnic WilsonLimitConstruction.FundedMarkedFieldSplit QLocalMarkedJoinedCatalogue QLocalThermalPacketDivision
local notation "newD" => (ActualOriginalQPointSetup.request R fresh.labels fresh.request).tests
local notation "raw" => ActualOriginalQInitialInput.packets R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
local notation "coupling" => regulatorRun R.family N p (m+1)

open Extra.Iteration.Comparison ActualWilsonDirtyPartners
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG fresh.labels fresh.request fresh.schedule
local notation "off₀" => ActualOriginalQInitialInput.cover R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
local notation "oldG" => regulatorRun R.family N p (m+2)
local notation "κ" => Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1))
local notation "k₀" => R.family.path.levels.clock.forcedAllowance (m+1)
local notation "B₀" => (A₀).inputNorm m
local notation "amt" => (A₀).admittedCost m
local notation "incl" => WilsonRootedTwoDateHardSource.inclusion (D:=newD) (tests)


open OriginalMarkedRunAction WilsonRootedInteriorPhysicalExponent

def Docket (s : ℝ) (prev d : ℕ) : Prop :=
    ∃τ : ℝ,0<τ ∧ τ≤1 ∧ ∃b : Overlay.Bands (Γ) (Y),b.origins=fresh.roots ∧ b.units=0 ∧ b.Active ∧ Seed.RadialReceipt b τ prev ∧
    0<s ∧ s≤1 ∧
    ∃A : Compulsory (LocalComparison.TestSpace (tests) × LocalComparison.TestSpace (newD)) (Γ) G (R.family.side (m+1) p),
      let T := WilsonRootedTwoDateIndependentHard.before fresh (tests) b
      let radii := WilsonRootedTwoDateHardRadius.smaller s (WilsonRootedTwoDateHardRadius.smaller τ (oneW))
      let before := (Real.sqrt 2*oldG)^(prev+1)
      FunctionalRetains (replace T A) (fun v=>{fresh.roots v}) ∧
      Nonempty (ForcedBudget (B₀) (pullback (incl) (replace T A)) radii (κ)
        (s*before+QLocalThermalJoinedForcedRegister.increase (raw) (B₀) (off₀) (s*(τ*(amt))) (κ) (k₀) (s*before))) ∧
      (∀ z : (Γ).Mode,((s*τ)^z.val.card)⁻¹*Poly.toll radii z=1) ∧
      WilsonRootedTwoDateHardIncome.Earned (raw) (B₀) (pullback (incl) (replace T A)) (off₀) s τ (κ) before (k₀) (amt) ∧
      let kept := approximation R (p:=p) old.below d
      let omitted := remainder R (p:=p) old.below d
      omitted.EBound (Y).p ((Real.sqrt 2*oldG)^(d+1)) ∧
      (∀ U,Summable (fun i=>kept.activities.regularOccurrence (Y).p i U) ∧ Summable (fun i=>omitted.regularOccurrence (Y).p i U)) ∧
      ∀(x : LocalComparison.TestSpace (tests)) (y : IndependentTests (newD)) U (L : List (Piece G (R.family.side (m+1) p))),
        Poly.pass ((raw).read (testInclusion (newD) y) (coupling) U)*old.ambient_response hG x U=
          Poly.pass (ManuscriptQLocalOriginalConditionalTail.source (raw) (Y).p (coupling) y 1 U)*
          ((Real.exp ((kept.activities.additive (Y).p U - Render.renders (Render.prefactor (coupling)) (Y).p U L)+omitted.additive (Y).p U) *
            (renderedWeight R (N:=N) L U)⁻¹) • ((replace T A).leaf (x,testInclusion (newD) y)).density U)

theorem purchased {ε γ : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {J : Request V}
    {extra : Stage → ℕ → ℝ} {order : ℕ → ℕ → ℕ} {scalar : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit}
    (book : WilsonRootedPhysicalSpringGaussian.Receipt.{u} hG ε J extra γ order R T W scalar)
    (A : NumericSchedule R.family J) (cap : J.inputSupport≤100) (u v : V→MS.Rake.Label B) (prev now q d : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop, let s := WilsonRootedTwoDateHardClock.rate R J v A m
    0<s ∧ s≤1 ∧ ∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v → fresh.request=J →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      fresh.schedule.admittedCost m≤A.admittedCost m →
      Docket old fresh hG s prev d ∧
      ∀ x : IndependentTests (ActualOriginalQPointSetup.request R old.labels old.request).tests,
        Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U)) (scene R.family.path N p (m+1)) ∧
        ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U) ∂scene R.family.path N p (m+1) ≤ η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedTwoDatePhysicalHard.original hG book.original book.spring book.marker u v prev now q positive,
    WilsonRootedTwoDateHardHeadroom.selected hG book.spring book.orders J cap,
    WilsonRetainedPaidCourse.selected_norm book.spring book.orders J cap,
    WilsonRootedTwoDateHardClock.previous R hG prev,
    (tendsto_add_atTop_nat 1).eventually (WilsonRootedInteriorPhysicalExponent.calendar R hG book.marker book.checkout d)] with m hard solvent fit prevSmall history
  have radius := WilsonRootedTwoDateHardClock.positive R J v A m
  refine ⟨radius.1,radius.2,?_⟩
  intro N p old fresh oldu freshv request layout room
  obtain ⟨_,issued,tested⟩ := hard N p old fresh oldu freshv layout
  subst J
  subst v
  obtain ⟨bank,allowance⟩ := solvent N p fresh.below fresh.schedule
  obtain ⟨τ,ht,one,b,roots,units,active,radial,ps,so,catalogue,ret,wallet,restore,earned,read⟩ :=
    WilsonRootedTwoDateHardFixed.at_step old fresh hG A prev room (prevSmall N p old.below) issued (fit N p fresh.below fresh.schedule) bank allowance
  obtain ⟨price,rows⟩ := history N p old.below
  refine ⟨⟨τ,ht,one,b,roots,units,active,radial,ps,so,catalogue,ret,wallet,restore,earned,price,fun U=>⟨(rows U).1,(rows U).2.1⟩,?_⟩,tested⟩
  intro x y U L
  apply (read x y U).trans
  apply congrArg (fun z : ℝ => _ * (z • _))
  exact (rendered_inverse R (N:=N) L U).trans (congrArg (fun δ : ℝ => Real.exp δ * (renderedWeight R (N:=N) L U)⁻¹) ((rows U).2.2 L))

end YM.Integration.WilsonRootedTwoDateHardPrepaid
