import YM.Integration.WilsonAddressedPublicSubmittedPort
import YM.Integration.WilsonCapturedPrimaryWeakTrialSubmittedOrder
import YM.Integration.WilsonPositionThermometerGradedSource

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicSubmittedDates
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCollarElection
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection WilsonIndependentCollarAddressedSource Comparison.Density.Transport Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal QuadraticLocal.Mentor
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
  {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{U:Type}[Fintype U]


open Marker Multi QuadraticLocal QuadraticLocal.Earn

open WilsonOriginalCensusDatedSchools (Paired)
open WilsonOriginalCensusMeasuredStation (CreditAt)
open WilsonCoeffUV.Bank.Carp

open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed recenter)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonOriginalCensusFaceIncome (addressed)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalCensusFixedBank (Income)


open WilsonOriginalFixedTestCensusPublicBase (base)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express


local notation "H" i:max => R.family.path.levels.clock.hatBeta (i)
local notation "levelsOf" => R.family.path.levels
local notation "tickets" M:max b:max geom:max => fun v=>b v*max 1
  (WilsonOriginalMixedBlockBudget.roots geom (WilsonIndependentCollarMaterialWallet.bill M b))

abbrev grades {n:ℕ} (role : Fin n → Fin 3) (v : Fin n) : ℕ :=
  (WilsonPositionThermometerGradedSource.grade (role v)).val

theorem positive {n:ℕ} (role : Fin n → Fin 3) (v : Fin n) : 0 < grades role v :=
  Fin.cases (motive:=fun i=>0 < (WilsonPositionThermometerGradedSource.grade i).val)
    (by decide) (fun _=>by simp [WilsonPositionThermometerGradedSource.grade]) (role v)

def Placed {n:ℕ}(d lens : Fin n → ℕ)(pt : Fin n → Chamber)(B δ σ : ℝ)
    (m j N per q : ℕ)(V : Realm G (q+1) Credit.leanC)(draw : V.draws=R.family.path.levels)
    (digits : Digits V.draws (Fin n))(seed : (v : Fin n)→ Choice R d v)
    (y : Fin n → Cover) : Prop :=
    let cap := fun v=>‖present lens v‖
    let power := fun _ : Fin n => 0
    let side := R.family.side (j+1) per
    let geom := binder side y
    let b := WilsonOriginalFixedTestCensusPublicBase.base B cap power (R.family.path.levels.clock.hatBeta (j+1))
    ∃L : Material R N (j+1) q d σ geom,
      Account V ((Real.sqrt (R.family.path.β N per (m+1)))^δ*B^n) δ side y L (present lens) ∧ L.tests=lens ∧
      Addressed y L (present L.tests) ∧
      (∀z S, output L.prior S N z =
        fixed R d (fun v=>contact (L.tests v)) pt N (j+2) (j+1) (onLevels draw digits) seed z S) ∧
      (∀S : Hot (Stock.census (Fin n)), Real.exp (σ*(geom S).length)*
        WilsonIndependentCollarSlateIntensity.amount (words L S) (geom S).center ≤
          WilsonIndependentCollarMaterialIntensity.price L S) ∧
      (∀v,0 < b v) ∧ (∀v,(tickets L b geom) v ≤ (R.family.path.levels.clock.hatBeta (j+1))^(power v+4)) ∧
      ∀(x : Affinity.Wallet (room (Fin n))) (S : Hot (Stock.census (Fin n))) (a : ℕ)
        (Y : Link G side), sideValue L (fun v=>contact (L.tests v)) pt (j+2)
          (onLevels draw digits) seed x false S a Y =
        (∏v∈S.val.val,(x v).val)*Complex.ofReal (diagonal (mass d S.val.val+a)
          (fun r z=>(touch (present L.tests) S.val.val)
            (plume ((fixed R d (fun v=>contact (L.tests v)) pt N (j+2) (j+1)
              (onLevels draw digits) seed y S.val.val).2 a r) side z)) Y)

theorem original (cash : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (seller : ℕ→Gear G→ℝ)(funded : FundedMarkedCoverRows.prices seller R.kit)
    {n : ℕ}(front : Fin n)(role : Fin n→Fin 3)(lens : Fin n→ℕ)(pt : Fin n→Chamber)
    (hd : ∀v, grades role v < lens v)(A : ℕ)(retained : ℕ→ℕ)
    (semester P : ℕ)(ht : 1 ≤ Burn.horizon semester)(slots : n ≤ Burn.horizon semester)
    (tube : LinkTube G)(pieces physical : ℕ)(p : Bool→ℕ)(span : U→ℕ)(lag : U→Bool→ℕ) :
    let d := grades role
    let q := retained A
    let θ := Burn.horizon semester
    let roots := WilsonOlderFreshGraphSchool.roots (menu (teacher (prepared s))) simple R.metals.p R.metals.K
    ∃B : ℝ, 1 ≤ B ∧ ∀ᶠ first : ℕ in atTop, ∃V : Realm G (q+1) Credit.leanC,
      ∃draw : V.draws = (levelsOf), V.paid=R.metals.O ∧ V.anchor=first ∧ ∃C : ℝ, 0 ≤ C ∧
        ∀δ : ℝ, 0 < δ → δ ≤ 1 → ∀ᶠ m : ℕ in atTop,
          (∀j≥m,WilsonIndependentCollarDatedTeachers.At s R simple V lens d θ P δ tube pieces physical p span lag j ∧
            WilsonIndependentCollarDatedTeachers.At s R simple V lens d θ P δ tube pieces physical p span lag (j+1)) ∧
          ∀(_hm : V.anchor ≤ m)(days : ℕ), 2 ≤ days →
            (levelsOf).S.scale (m+days)-(levelsOf).S.scale m ≤ (A:ℝ)*(1+Real.log (H (m+1))) →
            let j := m+days-2
            let σ := Poetry.Agenda.seed roots MintClock.splits θ ((levelsOf).clock.J (j+1))
            ∀ᶠ per : ℕ in atTop, ∀N, m+days ≤ N →
              (∀(digits : Digits V.draws (Fin n))(seed : (v:Fin n)→ Choice R d v)(y : Fin n→ Cover),
                Placed (R:=R) d lens pt B δ σ m j N per q V draw digits seed y) ∧
              ∀v:(l:Fin n)→R.family.label (d l),
                let all : Finset (Fin n) := univ
                let g := regulatorRun R.family N per (m+days)
                let scale := (levelsOf).S.a m/(levelsOf).S.a (m+days)
                let total := ∑l:all,d l
                let heat := Real.sqrt (R.family.path.β N per (m+1))
                ∑z:(l:all)→ Choice R d l,(∏l:all,WilsonIndependentCollarOriginalDose.weight
                      R d N per (m+days) v l (z l) g scale)*(heat^δ*B^all.card) ≤
                  (∏l:all,WilsonIndependentCollarOriginalDose.axisFee R d v l)*C^total*
                    heat^((2*A+1)*total)*(heat^δ*B^all.card) := by
  intro d q θ roots
  let cap := fun v=>‖present lens v‖
  have bank := eventually_atTop.1 (WilsonOriginalCensusFixedBank.original (k:=d) R
    (fun v=>contact (lens v)) pt simple cash.quiet seller funded q)
  obtain ⟨B,one,book⟩ := WilsonCapturedPrimaryWeakTrialSubmittedOrder.original cash n front d lens
    (fun v=>contact (lens v)) pt cap (fun v=>norm_nonneg _) hd A retained θ P ht slots tube
    pieces physical p span lag
  have finance := eventually_atTop.1 (WilsonAddressedPublicSubmittedPort.original (q:=q)
    R simple d B cap one (fun _=>0) (positive role))
  refine ⟨B,one,?_⟩
  filter_upwards [book] with first base
  obtain ⟨V,draw,wake,anchor,C,cp,course⟩ := base
  refine ⟨V,draw,wake,anchor,C,cp,?_⟩
  intro δ dp ds
  filter_upwards [course δ dp,eventually_ge_atTop bank.choose,eventually_ge_atTop finance.choose]
    with m paid fundedRows fundedFinance
  refine ⟨paid.1,?_⟩
  intro hm days room duration j σ
  have last : j+2=m+days := by dsimp [j]; omega
  have young : m ≤ j := by dsimp [j]; omega
  filter_upwards [paid.2 hm days duration (fun _=>0) (fun _ _=>1) (fun _ _=>zero_lt_one)] with per fresh
  intro N cut
  have full := fresh N cut (by omega)
  refine ⟨?_,full.2.2.2⟩
  intro digits seed y
  have enrolled := full.1 j young (by omega)
  rw [← last] at enrolled
  exact finance.choose_spec m fundedFinance j young N per (by omega) lens pt δ σ V draw
    digits seed y (by simpa only [Finset.card_univ,Fintype.card_fin] using enrolled) (bank.choose_spec j (fundedRows.trans young)) dp.le ds (by simp [cap])

end YM.Integration.WilsonAddressedPublicSubmittedDates
end
