import YM.Integration.WilsonOriginalMicroscopicGuardedEntrance
import YM.Integration.WilsonReflectedOpticalArm

/-! The three public trial arms share one physical date chosen before either regulator.
The native price covers each signed regular, forced, projected and scalar account. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceArmFare
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
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)

local notation "level" => R.family.path.levels
local notation "lattice" => R.family.S.a
local notation "beta" => R.family.path.levels.clock.hatBeta

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (d:Fin 3 → ℕ)(q B cap:ℕ)(grades:∀a,d a ≤ cap){ε:ℝ}(pos:0<ε):
    ∃cash:Fin 3 → ℝ,(∀a,0<cash a) ∧ ∃floor:ℕ,∀(j:Fin 3 → ℕ)(target:ℕ)(V:Fin 3 → ℝ)
      (Y:∀a:Fin 3,ℕ×ℕ → (C).label (d a)),(∀a,0 ≤ V a) → (∀a,floor ≤ j a) →
      Finished R d j target (1/32) (fun a=>(lattice (j a))^(d a)*V a) Y →
      ∀f (part:∀a,j a ≤ f),(∀a,lattice (j a)/lattice f ≤ (beta f)^B) →
      (∀a,((level).budget (j a)).supportExponent ≤ 100) → ((level).budget f).supportExponent ≤ 100 →
      let t:=WilsonReflectedOpticalRate.depth (q+2) B cap
      let K:=berth R t f
      ∃start:f<K,(beta f)^t ≤ lattice f/lattice K ∧ lattice f/lattice K ≤ (beta f)^t*(beta f)^ε ∧
      ∀N p (live:K ≤ N),
      ∃A:∀a:Fin 3,(C).label (d a) ≃ₗ[ℂ] (C).label (d a),
        (∀a x,Arrived R (d a) (j a) K N p target ((part a).trans start.le) live (1/32) (A a) x) ∧
        Placed R d j Y f (K-f) N p (by omega) A ∧
        ∀(spin:Fin 3 → Bool)(rot:Fin 3 → Signed)(o:Fin 3 → Site ((C).side f p)),
        ∃Z:∀a,Arm R (d a) N p f K,
          (∀a,(Z a).Y=Y a (N,p) ∧ (Z a).w=(A a).symm (full R (d a) N p (j a) (Y a (N,p))) ∧
            (Z a).b=spin a ∧ (Z a).s=rot a ∧ (Z a).o=o a ∧
            Priced R (Z a) (cash a*((beta f)^q)⁻¹*(lattice f)^(d a)*V a)) ∧
          Heard R d Z start.le live:=by
  classical
  choose cash positive floor buy using fun a=>WilsonReflectedOpticalArm.funded R simple slow q B cap (d a) (grades a) pos
  obtain ⟨g,grid⟩:=WilsonReflectedGuardedGrid.original R simple d
  let common:=max g (max (univ.sup floor) (univ.sup (fun a=>(C).ref (d a))))
  refine ⟨cash,positive,common,?_⟩
  intro j target V Y vp mature done f part span rough paid
  have floors(a:Fin 3):floor a ≤ j a:=
    (le_sup (f:=floor) (mem_univ a)).trans ((le_max_left ..).trans ((le_max_right ..).trans (mature a)))
  let t:=WilsonReflectedOpticalRate.depth (q+2) B cap
  have seats(a:Fin 3):=buy a (j a) (floors a) f (part a) (span a) (rough a) paid
  choose late lower upper fare using seats
  refine ⟨late 0,lower 0,upper 0,?_⟩
  have atDate (K:ℕ)(start:f<K)(N p:ℕ)(live:K≤N):
      ∃A:∀a:Fin 3,(C).label (d a) ≃ₗ[ℂ] (C).label (d a),
        (∀a x,Arrived R (d a) (j a) K N p target ((part a).trans start.le) live (1/32) (A a) x) ∧
        (∀a,WilsonReflectedFullPanel.receipt R (d a) (j a) K N p target ((part a).trans start.le) live
          (1/32) (A a) (Y a (N,p)) ((lattice (j a))^(d a)*V a)) ∧ Placed R d j Y f (K-f) N p (by omega) A:=by
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le start.le
    obtain ⟨A,ar,panels,placed⟩:=grid j target (1/32) (fun a=>(lattice (j a))^(d a)*V a) Y
      (fun a=>(le_max_left ..).trans (mature a)) done f n N p part live (fun a=>(part a).trans_lt (start.trans_le live))
    exact ⟨A,ar,panels,by simpa using placed⟩
  intro N p live
  obtain ⟨A,arrived,panels,placed⟩:=atDate (berth R t f) (late 0) N p live
  refine ⟨A,arrived,placed,?_⟩
  intro spin rot o
  choose Z bought using fun a=>fare a N p target live (A a) (Y a (N,p)) (V a) (vp a) (panels a) (spin a) (rot a) (o a)
  refine ⟨Z,bought,?_⟩
  have ref(a:Fin 3):(C).ref (d a) ≤ f:=
    (le_sup (f:=fun b=>(C).ref (d b)) (mem_univ a)).trans ((le_max_right ..).trans
      ((le_max_right ..).trans ((mature a).trans (part a))))
  intro s u uf W
  exact WilsonOriginalMicroscopicEntranceArmLaw.original R d Z (late 0).le live ref s uf W

end YM.Integration.WilsonOriginalMicroscopicEntranceArmFare
end
