import YM.Integration.WilsonOriginalMicroscopicEntranceFlatSchool
import YM.Integration.WilsonOriginalMicroscopicEntranceMarginals
import YM.Integration.WilsonOriginalMicroscopicGuardedStandingTrial

/-! A given public panel fixes its three physical source columns before any
requested accuracy. Their common dated assessment measures those columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatPublic
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
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((level).budget i).supportExponent)(quote:Poetry level)
    (φ:Test 3)(d:Fin 3→ℕ)(c q r ℓ B cap:ℕ)(grades:∀a,d a≤cap){ε:ℝ}(pos:0<ε):
    ∃cash:Fin 3→ℝ,(∀a,0<cash a) ∧ ∃ear:ℕ,∃floor:ℕ→ℕ,∀(ρ quota:Fin 3→ℝ)(b m:Fin 3→ℕ),
      (∀a,0≤quota a)→(∀a,Receipt F l (ρ a) (b a) (m a) (d a) (quota a))→
      ∃Y:∀a:Fin 3,S.Field (d a)→ℕ×ℕ→(C).label (d a),
      (∀a,Press R F (l:=l) (ρ a) (b a) (m a) (d a) (quota a) (Y a)) ∧
      ∀(v:∀a:Fin 3,S.Field (d a))(target:ℕ),(∀a,floor target≤b a)→
      (∀a,Named R F (l:=l) (ρ a) (b a) (m a) (d a) target (quota a) (v a) (Y a (v a))) ∧
      let V:=fun a=>quota a*cost F (d a) (ρ a) (v a)
      ∀f (prior:∀a,b a≤f),(∀a,lattice (b a)/lattice f≤(beta f)^B)→
      (∀a,((level).budget (b a)).supportExponent≤100)→((level).budget f).supportExponent≤100→
      let q₀:=q+2*ℓ+cap
      let t:=WilsonReflectedOpticalRate.depth (q₀+2) B cap
      let K:=berth R t f
      ∃early:f<K,(beta f)^t≤lattice f/lattice K ∧ lattice f/lattice K≤(beta f)^t*(beta f)^ε ∧
        ∀N p (live:K≤N),∃D:∀a:Fin 3,(C).label (d a)≃ₗ[ℂ](C).label (d a),
        (∀a x,Arrived R (d a) (b a) K N p target ((prior a).trans early.le) live (1/32) (D a) x) ∧
        Placed R d b (fun a=>Y a (v a)) f (K-f) N p (by omega) D ∧
        WilsonOriginalMicroscopicEntranceMarginals.Spent R φ c q ℓ ear d b (fun a=>Y a (v a)) (f:=f) (n:=K-f) (N:=N) (p:=p)
          (by omega) D (fun a=>cash a*V a) (fun a=>cash a*((beta f)^q₀)⁻¹*(lattice f)^(d a)*V a):=by
  obtain ⟨cash,positive,ear,head,buy⟩:=WilsonOriginalMicroscopicEntranceFlatSchool.original R κ pt simple slow cater bank book φ d c q r ℓ B cap grades pos
  obtain ⟨floor,menu⟩:=WilsonOriginalMicroscopicGuardedStandingTrial.original R F (l:=l) simple shop wide quote d
  let η:{x:ℝ //0<x}:=⟨1/32,by norm_num⟩
  refine ⟨cash,positive,ear,fun target=>max head (floor target η),?_⟩
  intro ρ quota b m qp receipts
  obtain ⟨Y,press,booked⟩:=menu ρ quota b m receipts
  refine ⟨Y,press,?_⟩
  intro v target late
  obtain ⟨named,finished⟩:=booked v target η (fun a=>(le_max_right ..).trans (late a))
  refine ⟨named,?_⟩
  intro V f prior span upper₁ upper₂ q₀ t K
  have vp(a:Fin 3):0≤V a:=mul_nonneg (qp a) (cost_pos ..)
  have room:Finished R d b target (1/32) (fun a=>(lattice (b a))^(d a)*V a) (fun a=>Y a (v a)):=by
    simpa only [V,WilsonOriginalMicroscopicGuardedNomination.budget,mul_assoc] using finished
  obtain ⟨early,lo,hi,priced⟩:=buy b target V (fun a=>Y a (v a)) vp (fun a=>(le_max_left ..).trans (late a)) room f prior span upper₁ upper₂
  refine ⟨early,lo,hi,?_⟩
  intro N p live
  obtain ⟨D,arrived,placed,issued⟩:=priced N p live
  exact ⟨D,arrived,placed,WilsonOriginalMicroscopicEntranceMarginals.original R issued⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatPublic
end
