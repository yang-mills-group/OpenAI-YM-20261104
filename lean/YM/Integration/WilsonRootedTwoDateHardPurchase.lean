import YM.Integration.WilsonRootedTwoDateHardFamily
import YM.Integration.WilsonRootedTwoDateHardPrice
import YM.Integration.WilsonRootedTwoDateHardMargins
import YM.Integration.WilsonRootedTwoDateHardOld
import YM.Integration.WilsonRootedTwoDateHardHeadroom
import YM.Integration.WilsonRootedTwoDatePhysicalHard
import YM.Integration.WilsonRootedTwoDateFreshExponent

/-! The same signed hard catalogue recovers the raw two-date field and pays every independent tested row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardPurchase
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

/-- The two-test budget belongs to the very compulsory register used in the physical density. -/
def Bought (prev : ℕ) : Prop :=
    ∃τ : ℝ,0<τ ∧ τ≤1 ∧ ∃b : Overlay.Bands (Γ) (Y),b.origins=fresh.roots ∧ b.units=0 ∧ b.Active ∧ Seed.RadialReceipt b τ prev ∧
    ∃s : ℝ,0<s ∧ s≤1 ∧
    ∃A : Compulsory (LocalComparison.TestSpace (tests) × LocalComparison.TestSpace (newD)) (Γ) G (R.family.side (m+1) p),
      let T := WilsonRootedTwoDateIndependentHard.before fresh (tests) b
      let radii := WilsonRootedTwoDateHardRadius.smaller s (WilsonRootedTwoDateHardRadius.smaller τ (oneW))
      let before := (Real.sqrt 2*oldG)^(prev+1)
      FunctionalRetains (replace T A) (fun v=>{fresh.roots v}) ∧
      Nonempty (ForcedBudget (B₀) (pullback (incl) (replace T A)) radii (κ)
        (s*before+QLocalThermalJoinedForcedRegister.increase (raw) (B₀) (off₀) (s*(τ*(amt))) (κ) (k₀) (s*before))) ∧
      (∀ z : (Γ).Mode,((s*τ)^z.val.card)⁻¹*Poly.toll radii z=1) ∧
      ∀(x : LocalComparison.TestSpace (tests)) (y : IndependentTests (newD)) U,
        Poly.pass ((raw).read (testInclusion (newD) y) (coupling) U)*old.ambient_response hG x U=
          Poly.pass (ManuscriptQLocalOriginalConditionalTail.source (raw) (Y).p (coupling) y 1 U)*
          (((Y).eval U)⁻¹ • ((replace T A).leaf (x,testInclusion (newD) y)).density U)

theorem at_step (prev : ℕ) (oldPaid : WilsonRootedTwoDatePhysicalHard.Paid old fresh hG prev)
    (fit : HasBudget (Y).p (B₀)) (bank : (Y).activities.KBound (B₀) (k₀))
    (allowance : 2*(k₀)*blockSites (B₀).B≤(B₀).supportExponent) : Bought old fresh hG prev := by
  obtain ⟨τ,ht,one,b,roots,units,active,radial,read,_,_⟩ := oldPaid
  let T := WilsonRootedTwoDateIndependentHard.before fresh (tests) b
  let K := OriginalForcedAddresses.actual_keeper R hG N (m+1) p fresh.below
  have div : 0<(κ) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have H := ActualOriginalQInitialInput.paid R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
  have hg := (IterationFour.Currency.g_pos R.makes N p (m+1) fresh.below).ne'
  obtain ⟨start⟩ := WilsonRootedTwoDateHardOld.original (tests) (newD) b fit div active radial
  obtain ⟨s,ps,so,hnew,⟨hold⟩,small,room,restore⟩ :=
    WilsonRootedTwoDateHardMargins.sold (raw) (pullback (incl) T) H start ht one allowance
  obtain ⟨L,ret,all,_⟩ := WilsonRootedTwoDateHardFamily.original fresh hG (tests) b roots active radial
  have money : 0 ≤ s * (τ * (amt)) := mul_nonneg ps.le (mul_nonneg ht.le (Push.AbsoluteSums.budget_nonneg (H.roots (Classical.arbitrary V))))
  have valid := (R.makes.wilson.represents N p (m+1) fresh.below).good.labels.forced
  have point (v:V) : b.origins v∈({fresh.roots v}:Support (R.family.side (m+1) p)) := by simp [roots]
  have wallet := WilsonRootedTwoDateHardPrice.registered (raw) (tests) K hnew money hg point (1:ℂ) (by simp) T L valid
    (fun z=>WilsonOriginalPointTaste.active (tests) b active z.1) div bank hold small room
  refine ⟨τ,ht,one,b,roots,units,active,radial,s,ps,so,L.book,ret,wallet,restore,?_⟩
  intro x y U
  let oldValue := ((WilsonOriginalPointTaste.representation (tests) b).leaf x).density U
  let cold := Poly.pass (ManuscriptQLocalOriginalConditionalTail.source (raw) (Y).p (coupling) y 1 U)
  let hot := Poly.pass (dirty (raw) (Y).p (testInclusion (newD) y) (coupling) U)
  have raw_eq : Poly.pass ((raw).read (testInclusion (newD) y) (coupling) U)=cold*hot :=
    WilsonRootedTwoDateFreshExponent.original (raw) (Y).p H hg y U
  have hard := ((all (x,testInclusion (newD) y)).2.2 U).2
  calc
    _ = (cold*hot)*(((Y).eval U)⁻¹ • oldValue) := congrArg₂ (·*·) raw_eq (read x U)
    _ = cold*(hot*(((Y).eval U)⁻¹ • oldValue)) := mul_assoc ..
    _ = cold*(((Y).eval U)⁻¹ • (hot*oldValue)) := by rw [mul_smul_comm]
    _ = _ := congrArg (fun z=>cold*(((Y).eval U)⁻¹ • z)) hard.symm

end YM.Integration.WilsonRootedTwoDateHardPurchase
