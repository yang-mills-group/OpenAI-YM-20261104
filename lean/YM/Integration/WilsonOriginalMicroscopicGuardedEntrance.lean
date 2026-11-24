import YM.Integration.WilsonOriginalMicroscopicEntranceArmLaw
import YM.Integration.WilsonReflectedGuardedGrid

/-! One before-test source election, with the three actual reporter matrices,
the located cutoff fields and three guarded K stencils at their own sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedEntrance
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedGridSchool WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonReflectedFundedHearing (Arm cropped signed)
open WilsonOriginalMicroscopicEntranceArms (physical)
open WilsonOriginalMicroscopicEntranceEarlier (face)
open WilsonOriginalMicroscopicEntranceArmLaw (hearing)
open Marker OPE.Therm
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)

def Heard (d:Fin 3 → ℕ){N p f K:ℕ}(Z:∀a,Arm R (d a) N p f K)(start:f ≤ K)(live:K ≤ N):Prop:=
  ∀(s:(J).Mode){u:ℕ}(prior:u ≤ f)(W:Config G ((C).side u p)),
    let X:=fun a=>physical R (Z a) (start.trans live)
    let B:=fun a=>cropped R (Z a) start
    let H:=hearing R Z start live s
    let E:=actualTransport (C) (N:=N) (face X s) (prior.trans (start.trans live)) W-
      actualTransport (C) (N:=N) (face B s) (prior.trans start) W
    E=actualTransport (C) (N:=N) H prior W ∧ ‖E‖ ≤ actualTransport (C) (N:=N) (fun U=>‖H U‖) prior W

theorem original (simple:G.Simple)(d:Fin 3 → ℕ):∃floor:ℕ,∀(j:Fin 3 → ℕ)(target:ℕ)(η:ℝ)(M:Fin 3 → ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ → (C).label (d a)),
    (∀a,floor ≤ j a) → Finished R d j target η M Y →
    ∀f n N p (part:∀a,j a ≤ f)(live:f+n ≤ N), (∀a,j a<N) →
    ∃A:∀a:Fin 3,(C).label (d a) ≃ₗ[ℂ] (C).label (d a),
      (∀a x,Arrived R (d a) (j a) (f+n) N p target (Nat.le_add_right_of_le (part a)) live η (A a) x) ∧
      Placed R d j Y f n N p live A ∧
      ∀(spin:Fin 3 → Bool)(rot:Fin 3 → Signed)(o:Fin 3 → Site ((C).side f p)),
      ∃Z:∀a,Arm R (d a) N p f (f+n),
        (∀a,(Z a).Y=Y a (N,p) ∧ (Z a).w=(A a).symm (full R (d a) N p (j a) (Y a (N,p))) ∧
          (Z a).b=spin a ∧ (Z a).s=rot a ∧ (Z a).o=o a ∧
          (Z a).cash=hike (C) (f+n) f rate*((1+4*stock (C) (f+n))*((C).labels.level (d a)).coeffSize (Z a).w)) ∧
        Heard R d Z (Nat.le_add_right f n) live:=by
  obtain ⟨c,funded⟩:=WilsonReflectedGuardedGrid.original R simple d
  let cover:=univ.sup (fun a=>(C).ref (d a))
  refine ⟨max c cover,?_⟩
  intro j target η M Y old done f n N p part live join
  obtain ⟨A,arrived,all,placed⟩:=funded j target η M Y (fun a=>(le_max_left ..).trans (old a)) done f n N p part live join
  refine ⟨A,arrived,placed,?_⟩
  intro spin rot o
  have begun:f ≤ f+n:=Nat.le_add_right f n
  choose Z purchased using fun a=>WilsonReflectedFundedHearing.purchased R (d a) (j a) target
    (Nat.le_add_right_of_le (part a)) live (part a) begun (all a) (spin a) (rot a) (o a)
  refine ⟨Z,purchased,?_⟩
  have mature(a:Fin 3):(C).ref (d a) ≤ f:=
    (le_sup (f:=fun z=>(C).ref (d z)) (mem_univ a)).trans ((le_max_right ..).trans ((old a).trans (part a)))
  intro s u prior W
  exact WilsonOriginalMicroscopicEntranceArmLaw.original R d Z begun live mature s prior W

end YM.Integration.WilsonOriginalMicroscopicGuardedEntrance
end
