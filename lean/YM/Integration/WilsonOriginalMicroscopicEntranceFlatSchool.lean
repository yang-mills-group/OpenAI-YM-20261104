import YM.Integration.WilsonOriginalMicroscopicEntranceFlatReceiver

/-! All three folded trials and all actual flat signed ears reuse one native
coordinate choice on the very same public course and optical restart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatSchool
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

theorem original {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready level)(book:WilsonReportLampForecast.Ready level)
    (φ:Test 3)(d:Fin 3→ℕ)(c q r ℓ B cap:ℕ)(grades:∀a,d a≤cap){ε:ℝ}(pos:0<ε):
    ∃cash:Fin 3→ℝ,(∀a,0<cash a) ∧ ∃ear floor:ℕ,∀(b:Fin 3→ℕ)(target:ℕ)(V:Fin 3→ℝ)
      (Y:∀a:Fin 3,ℕ×ℕ→(C).label (d a)),(∀a,0≤V a)→(∀a,floor≤b a)→
      Finished R d b target (1/32) (fun a=>(lattice (b a))^(d a)*V a) Y →
      ∀f (prior:∀a,b a≤f),(∀a,lattice (b a)/lattice f≤(beta f)^B)→
      (∀a,((level).budget (b a)).supportExponent≤100)→((level).budget f).supportExponent≤100→
      let q₀:=q+2*ℓ+cap
      let t:=WilsonReflectedOpticalRate.depth (q₀+2) B cap
      let K:=berth R t f
      ∃early:f<K,(beta f)^t≤lattice f/lattice K ∧ lattice f/lattice K≤(beta f)^t*(beta f)^ε ∧
        ∀N p (live:K≤N),∃D:∀a:Fin 3,(C).label (d a)≃ₗ[ℂ](C).label (d a),
        (∀a x,Arrived R (d a) (b a) K N p target ((prior a).trans early.le) live (1/32) (D a) x) ∧
        Placed R d b Y f (K-f) N p (by omega) D ∧
        WilsonOriginalMicroscopicEntranceFlatReceiver.Issued R φ c q ℓ ear d b Y (f:=f) (n:=K-f) (N:=N) (p:=p)
          (by omega) D (fun a=>cash a*V a) (fun a=>cash a*((beta f)^q₀)⁻¹*(lattice f)^(d a)*V a):=by
  classical
  obtain ⟨cash,positive,cut,buy⟩:=WilsonOriginalMicroscopicEntranceGridPurchase.original R κ pt simple slow d (q+2*ℓ+cap) B cap grades pos
  obtain ⟨ear,settle⟩:=WilsonOriginalMicroscopicEntranceFlatReceiver.original R simple cater bank book φ c q r cap ℓ d grades κ pt
  let lower:=Finset.univ.sup (fun a:Fin 3=>(C).ref (d a))
  refine ⟨cash,positive,ear,max lower (max cut ear),?_⟩
  intro b target V Y vp late finished f prior span upper₁ upper₂ q₀ t K
  have starts(a:Fin 3):cut≤b a:=(le_max_left ..).trans ((le_max_right ..).trans (late a))
  have hears(a:Fin 3):ear≤b a:=(le_max_right ..).trans ((le_max_right ..).trans (late a))
  have mature(a:Fin 3):(C).ref (d a)≤f:=
    (Finset.le_sup (f:=fun a:Fin 3=>(C).ref (d a)) (Finset.mem_univ a)).trans
      ((le_max_left lower (max cut ear)).trans ((late a).trans (prior a)))
  obtain ⟨early,lo,hi,program⟩:=buy b target V Y vp starts finished f prior span upper₁ upper₂
  refine ⟨early,lo,hi,?_⟩
  intro N p live
  obtain ⟨D,arrived,placed,wages,financed⟩:=program N p live
  refine ⟨D,arrived,placed,?_⟩
  have hk:f+(K-f)=K:=Nat.add_sub_of_le (show f≤K from early.le)
  have source:f+(K-f)≤N:=by simpa only [hk] using live
  apply settle b hears target (1/32) Y f (K-f) N p source prior mature D
  · intro a x
    simp only [hk]
    exact arrived a x
  · exact fun a=>mul_nonneg (positive a).le (vp a)
  · intro a
    exact (wages a).trans_eq (by ring)
  · exact financed

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatSchool
end
