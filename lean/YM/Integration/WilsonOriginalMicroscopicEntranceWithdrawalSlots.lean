import YM.Integration.WilsonMeasuredPublicSlots
import YM.Integration.WilsonOriginalMicroscopicEntranceFlatWithdrawal
import YM.Integration.WilsonOriginalMicroscopicEntranceFlatSchool
import YM.Integration.WilsonOriginalMicroscopicEntranceMarginals
import YM.Integration.WilsonOriginalMicroscopicGuardedStandingTrial

/-! A given public panel fixes its three physical source columns before any
requested accuracy. Their common dated assessment measures those columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceWithdrawalSlots
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedGridSchool WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonReflectedFundedHearing (Arm cropped signed)
open WilsonOriginalMicroscopicEntranceArms (physical)
open WilsonOriginalMicroscopicEntranceEarlier (face)
open WilsonOriginalMicroscopicEntranceArmLaw (hearing)
open WilsonOriginalMicroscopicGuardedEntrance (Heard)
open WilsonInvariantActionPosition (berth)
open WilsonReflectedOpticalArm (Priced)
open Marker OPE.Therm
open WilsonOriginalMicroscopicEntranceFlatReceiver (Issued)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)

local notation "level" => R.family.path.levels
local notation "lattice" => R.family.S.a
local notation "beta" => R.family.path.levels.clock.hatBeta

open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiledPress OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds


open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination
open WilsonOriginalMicroscopicStandingLabels WilsonOriginalMicroscopicGuardedGridSchool
open OPE.Therm PhysicalNext OPE PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical Topology BigOperators
variable {ord:Extraction.Order}{S:Table R.family.book}(F:Final R.family ord S){l:Ultrafilter (ℕ×ℕ)}


theorem original {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready level)(book:WilsonReportLampForecast.Ready level)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1 ≤ ((level).budget i).supportExponent)(quote:Poetry level)
    (φ:Test 3)(d:Fin 3→ℕ)(c q r ℓ B cap:ℕ)(grades:∀a,d a ≤ cap){ε tol:ℝ}(pos:0<ε)(small:ε ≤ 1)(paid:0<tol):
    ∃cash:Fin 3→ℝ,(∀a,0<cash a) ∧ ∃ear:ℕ,∃floor:ℕ→ℕ,∀
      (v:∀a:Fin 3,S.Field (d a))(ρ quota:Fin 3→ℝ)(slots:∀a:Fin 3,WilsonMeasuredPublicSlots.Slot F l (d a) (v a) (ρ a) (quota a))
      (target:ℕ),(∀a,0 ≤ quota a)→(∀a,floor target ≤ (slots a).j)→
      let Y:=fun a=>(slots a).arm.source
      let dates:=fun a=>(slots a).j
      let V:=fun a=>quota a*cost F (d a) (ρ a) (v a)
      ∀f (prior:∀a,dates a ≤ f),(∀a,lattice (dates a)/lattice f ≤ (beta f)^B)→
      (∀a,((level).budget (dates a)).supportExponent ≤ 100)→((level).budget f).supportExponent ≤ 100→
      let q₀:=q+2*ℓ+cap
      let t:=WilsonReflectedOpticalRate.depth (q₀+2) B cap
      let K:=berth R t f
      ∃early:f<K,(beta f)^t ≤ lattice f/lattice K ∧ lattice f/lattice K ≤ (beta f)^t*(beta f)^ε ∧
        ∀N p (live:K ≤ N),∃D:∀a:Fin 3,(C).label (d a)≃ₗ[ℂ](C).label (d a),
        (∀a x,Arrived R (d a) (dates a) K N p target ((prior a).trans early.le) live (1/32) (D a) x) ∧
        Placed R d dates Y f (K-f) N p (by omega) D ∧
        WilsonOriginalMicroscopicEntranceFlatWithdrawal.Returned R φ simple tol c q ℓ ear d dates Y (f:=f) (n:=K-f) (N:=N) (p:=p)
          (by omega) D (fun a=>cash a*V a) (fun a=>cash a*((beta f)^q₀)⁻¹*(lattice f)^(d a)*V a):=by
  obtain ⟨cash,positive,ear,head,buy⟩:=WilsonOriginalMicroscopicEntranceFlatSchool.original R κ pt simple slow cater bank book
    φ d c q r ℓ B cap grades pos
  let τ:=WilsonReflectedOpticalRate.depth (q+2*ℓ+cap+2) B cap
  let stage:=(Filter.eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
    (q+WilsonOriginalMicroscopicEntranceHaloIncome.all R d (τ+1)) paid)).choose
  choose start stream using fun target:ℕ=>WilsonOriginalMicroscopicGuardedDated.original R simple shop wide quote d target (by norm_num : (0:ℝ)<1/32)
  refine ⟨cash,positive,ear,fun target=>max head (max stage (start target)),?_⟩
  intro v ρ quota slots target qp late Y dates V f prior spans upper₁ upper₂ q₀ t K
  have wage(a:Fin 3):0 ≤ V a:=mul_nonneg (qp a) (cost_pos ..)
  have ready:Finished R d dates target (1/32) (fun a=>(lattice (dates a))^(d a)*V a) Y:=by
    apply stream target dates (fun a=>(le_max_right stage (start target)).trans ((le_max_right ..).trans (late a)))
    intro a N p live
    simpa only [WilsonPositionProgramBlockedPublicExperiment.deposited,Next.UVStress.quota,Y,V,dates] using (slots a).numerical N p live
  obtain ⟨early,lo,hi,look⟩:=buy dates target V Y wage (fun a=>(le_max_left ..).trans (late a)) ready f prior spans upper₁ upper₂
  refine ⟨early,lo,hi,?_⟩
  intro N p live
  obtain ⟨D,arrived,placed,issued⟩:=look N p live
  refine ⟨D,arrived,placed,?_⟩
  have hk:f+(K-f)=K:=Nat.add_sub_of_le early.le
  have mature(a:Fin 3):(C).ref (d a) ≤ f:=(slots a).owns.trans (prior a)
  have note:stage ≤ f+(K-f):=by
    rw [hk]
    exact (le_max_left stage (start target)).trans ((le_max_right ..).trans ((late 0).trans ((prior 0).trans early.le)))
  have room:(lattice f)/(lattice (f+(K-f))) ≤ (beta (f+(K-f)))^(t+1):=by
    rw [hk]
    exact WilsonOriginalMicroscopicEntranceHaloIncome.optical R simple early.le small hi
  exact WilsonOriginalMicroscopicEntranceFlatWithdrawal.original R simple paid (fun a=>mul_nonneg (positive a).le (wage a))
    (WilsonOriginalMicroscopicEntranceFlatWithdrawal.fee R f q₀ d cash V (fun a=>(positive a).le) wage)
    mature room note (WilsonOriginalMicroscopicEntranceMarginals.original R issued)

end YM.Integration.WilsonOriginalMicroscopicEntranceWithdrawalSlots
end
