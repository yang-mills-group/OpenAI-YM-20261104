import YM.Integration.WilsonReceivedChronologicalFixedSelection
import YM.Integration.WilsonReceivedChronologicalFixedTariff
import YM.Integration.WilsonReceivedChronologicalFixedSchool
/-! One before-regulator physical interval with both independently posted ages on its actual older quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedWindow
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

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
open WilsonOriginalCensusAttendanceStation WilsonOriginalCensusPublicationClock

open Function Filter Finset Lattice RG RG.Supply Org PhysicalNext.Repeat Legato
open Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth QuadraticLocal.Sunrise.Aviary
open AllOrder.Transit AllOrder.Transit.WheelP
open WilsonOlderFreshGraphAward WilsonThermometerDeclaredSeeds
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedGeometric WilsonOriginalOccupiedForestIntegral
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonMarkedIndependentPhysicalIntake
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe
open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory

open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedCanonicalVerseBasis OriginalMarkedSourceComet
open Multi WilsonCoeffUV.Blue


open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedTariff (gross allowance)
open WilsonOriginalCensusFaceAdmission (housed)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonOriginalCensusDatedPeriodOpening (Opened)
open WilsonOriginalCensusDatedHeldTariff (Rates)
open WilsonOriginalFixedTestCensusPublicBase (base)
open WilsonOriginalCensusPublicationClock (Open)

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    (n:ℕ)(front:Fin n)(k D:Fin n → ℕ)(κ:(v:Fin n) → Knob (D v))(pt:Fin n → Chamber)
    (caps:Fin n → ℝ)(power:Fin n → ℕ)(nonneg:∀v,0 ≤ caps v)(hk:∀v,k v < D v)
    (P cost:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    let menu:=terms k power P
    let ask:=programme k power P
    let L:=R.family.path.levels
    let all:Finset (Fin n):=univ
    ∃book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple,
    ∃price:Credit,∃B:ℝ,1 ≤ B ∧ ∀ᶠ o:ℕ in atTop,
    WilsonSingleHardRadius.first R simple ≤ o ∧
    ∃resident:(N:ℕ) → o ≤ N → Day (prepared s) R simple ask.school o N,
    (∀N:ℕ,∀live:o ≤ N,∃Z:ℕ → SeriesA G,QuietAt (resident N live) price Z) ∧
    ∀ᶠ first:ℕ in atTop,∃V:Realm G (menu.order+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=first ∧ ∀A:ℕ,∃C:ℝ,0 ≤ C ∧ ∀δ:ℝ,0 < δ → δ ≤ 1 → ∀ᶠ m:ℕ in atTop,
      ∃old:o ≤ m,V.anchor ≤ m ∧ start k power P R simple cost tol η tp ep ≤ m ∧
      WilsonOriginalCensusSparseRosterOpening.first R simple tube k k (charges power) menu.order menu.order
        menu.target menu.precision menu.enough ≤ m ∧
      (∀j≥m,WilsonIndependentCollarDatedTeachers.At s R simple V D k (Burn.horizon ask.vac) school δ tube pieces physical p span lag j) ∧
      ∀(days:ℕ),3 ≤ days → L.S.scale (m+days)-L.S.scale m ≤ (A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) → 
      let K:=m+days
      let active:=Finset.Ico m (K-1)
      ∃rates:(a:active) → Rates R k κ pt (a.val+1) K menu.order,
      (∀a:active,WilsonOriginalCensusFixedBank.Income (k:=k) R κ pt menu.order (a.val+1)) ∧
      ∀ᶠ per:ℕ in atTop,
      (∀a:active,(∀cells:Digits V.draws (Fin n),let y:=homes cells 0 m (a.val-m)
        housed y R (a.val+1) per ∧ spread y ≤ diameter V n m (a.val-m)) ∧
        (∀(t:Hot (Stock.census (Fin n)))(e:Fin (menu.order+1)),
          Opened R (a.val+1) per (mass k t.val.val+e.val) ((rates a).width t.val.val e)
            ((rates a).fare t.val.val e) (gross caps) (WilsonReceivedChronologicalMaterialOpening.price R k (a.val+1) menu.precision)) ∧
        ∀t:Hot (Stock.census (Fin n)),CreditAt R κ pt k caps (a.val+1) K menu.order per (diameter V n m (a.val-m))
          (allowance R k menu.precision (a.val+1) t)) ∧
      ∀N:ℕ,∀valid:K ≤ N,
        let H:=Real.sqrt (R.family.path.β N per (m+1))
        let rate:=H^δ*B^n
        let oldDay:=resident N (by omega)
        (∀(cells:Digits V.draws (Fin n))(seed:(v:Fin n) → Choice R k v)(ground:Fin n → Cover)(t:Case D),
          (∀r:Hot (Stock.census (Fin n)),0 < mass k r.val.val) → 
          (∀j∈active,∀v,‖t v‖ ≤ caps v*(L.clock.hatBeta (j+1))^(power v)) → 
          Cohort (K:=K) (per:=per) (draw:=draw) (rate:=rate) (allowance:=δ) power P book oldDay cells t κ pt seed ground
            (fun j=>base B caps power (L.clock.hatBeta (j+1))) old valid) ∧
        ∀v:(l:Fin n) → R.family.label (k l),
          let scale:=L.S.a m/L.S.a K
          let d:=∑i:all,k i
          ∑z:(i:all) → Choice R k i,(∏i:all,WilsonIndependentCollarOriginalDose.weight R k N per K v i (z i)
              (regulatorRun R.family N per K) scale)*rate ≤ 
            (∏i:all,WilsonIndependentCollarOriginalDose.axisFee R k v i)*C^d*H^((2*A+1)*d)*rate:=by
  intro menu ask L all
  obtain ⟨book,price,_,B,one,courses⟩:=WilsonReceivedChronologicalFixedSchool.original paid paths n front k D κ pt caps power
    nonneg hk menu.order menu.rent ask school tube pieces physical p span lag
  refine ⟨book,price,B,one,?_⟩
  filter_upwards [courses,eventually_ge_atTop (WilsonSingleHardRadius.first R simple)] with o course ready
  obtain ⟨resident,quiet,rooms⟩:=course
  refine ⟨ready,resident,quiet,?_⟩
  filter_upwards [rooms] with first found
  obtain ⟨V,draw,paidV,anchor,wages⟩:=found
  refine ⟨V,draw,paidV,anchor,?_⟩
  intro A
  obtain ⟨C,cp,before⟩:=wages A
  refine ⟨C,cp,?_⟩
  intro δ dp ds
  filter_upwards [before δ dp ds,WilsonReceivedChronologicalFixedTariff.original paid k κ pt menu.order menu.precision caps,
    eventually_ge_atTop V.anchor,eventually_ge_atTop (start k power P R simple cost tol η tp ep),
    eventually_ge_atTop (WilsonOriginalCensusSparseRosterOpening.first R simple tube k k (charges power) menu.order menu.order
      menu.target menu.precision menu.enough)] with m funded winding begun salary scarce
  obtain ⟨old,_,board,_,teaching,issue⟩:=funded
  refine ⟨old,begun,salary,scarce,fun j hj=>(teaching j hj).1,?_⟩
  intro days many fits K active
  obtain ⟨rates,reserves,periods⟩:=winding K
  let dates:=Finset.Ico m K
  let di:dates → ℕ:=fun j=>diameter V n m (j.val-(m+1))
  let amount:dates → Hot (Stock.census (Fin n)) → ℝ:=fun j=>allowance R k menu.precision j.val
  have pass:=issue begun days many fits di amount (fun _ _=>WilsonReceivedChronologicalFixedTariff.positive ..)
  refine ⟨rates,reserves,?_⟩
  filter_upwards [periods V,pass] with per prices receipts
  refine ⟨?_,?_⟩
  · intro a
    obtain ⟨housed,opened⟩:=prices a
    refine ⟨housed,opened,?_⟩
    have access:=receipts K le_rfl (by omega)
    have available:=access.2.1
    let j:dates:=⟨a.val+1,by obtain ⟨lo,hi⟩:=Finset.mem_Ico.mp a.property; exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩⟩
    intro t
    simpa only [di,amount,j,Nat.add_sub_add_right] using available j t
  · intro N valid H rate oldDay
    obtain ⟨⟨_,grant⟩,_,dose⟩:=receipts N valid (by omega)
    refine ⟨?_,?_⟩
    · intro cells seed ground t deep bounded
      obtain ⟨M,income⟩:=grant cells seed ground t deep bounded
      exact WilsonReceivedChronologicalFixedSelection.original (K:=K) (per:=per) (draw:=draw) (rate:=rate)
        (allowance:=δ) power P book oldDay cells t κ pt seed ground
        (fun i=>base B caps power (L.clock.hatBeta (i+1))) M old valid
        (fun a=>(income a).1) (fun a=>(income a).2.1) (fun a=>(income a).2.2.1) (fun a=>(income a).2.2.2.2)
    · simpa only [all,L,K,H,rate,Finset.card_univ,Fintype.card_fin] using dose
end YM.Integration.WilsonReceivedChronologicalFixedWindow
end
