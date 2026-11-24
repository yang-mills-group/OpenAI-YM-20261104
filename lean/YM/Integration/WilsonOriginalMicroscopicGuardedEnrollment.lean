import YM.Integration.WilsonOriginalMicroscopicGuardedNomination
import YM.Integration.WilsonOriginalMicroscopicGuardedReporters

/-! One original Final and its cutoff labels pay the three measured columns.
The public fields and reporting dates are fixed before both regulators. At the
common upper date the inverse for each column serves all target labels. The
joint refund uses exactly its cutoff coordinate on that same run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedEnrollment
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open PhysicalNext OPE.Therm Push.AbsoluteSums.Animals Next.Foundations Trace.Physical Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C" => R.family

def coordinates (d j:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(C).label (d a))(N p:ℕ)(a:Fin 3):(C).label (d a):=
  (deposited R (d a) N p (j a) (Y a (N,p))).x

def Resolved (d j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→(C).label (d a)):Prop:=
  ∀K (before:∀a,j a ≤ K) N p (high:K ≤ N), (∀a,j a<N)→
    ∃A:∀a:Fin 3,(C).label (d a) ≃ₗ[ℂ] (C).label (d a),
    (∀a e,Arrived R (d a) (j a) K N p target (before a) high η (A a) e) ∧
    let e:=coordinates R d j Y N p
    let v:=fun a=>(A a).symm (e a)
    (∀a,((C).labels.level (d a)).coeffSize (v a) ≤ stretch R η (j a) K*M a) ∧
    ∀ (o:Fin 3→Site ((C).side K p))(s:Finset (Fin 3)) u (prior:u ≤ K),
      (∫U,‖actualTransport (C) (N:=N) (gap R d N p K o v s) prior U‖ ∂scene (C).path N p u) ≤
        invoice R d K (fun a=>stretch R η (j a) K*M a) s*(C).path.levels.clock.forcedAllowance K

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(bliss:Bliss F l Z H)
    (wide:∀j,1 ≤ ((C).path.levels.budget j).supportExponent)(quote:Poetry (C).path.levels)
    (d:Fin 3→ℕ)(target:ℕ){η:ℝ}(ep:0<η):
    ∃ T:Fin 3→ℕ,∃ready:Fin 3→Set ℝ,(∀a,ready a∈trail) ∧
    ∀r:Fin 3→ℝ,(∀a,r a∈ready a)→∃j m:Fin 3→ℕ,
      (∀a,Receipt F l (r a) (j a) (m a) (d a) (dock (r a)^(T a))) ∧
      ∀v:∀a:Fin 3,S.Field (d a),∃Y:∀a:Fin 3,ℕ×ℕ→(C).label (d a),
        (∀a,Named R F (l:=l) (r a) (j a) (m a) (d a) target (dock (r a)^(T a)) (v a) (Y a)) ∧
        Resolved R d j target η (fun a=>budget R F (d a) (r a) (j a) (dock (r a)^(T a)) (v a)) Y:=by
  obtain ⟨L,reports⟩:=WilsonOriginalMicroscopicGuardedReporters.original R d simple shop wide quote target ep
  obtain ⟨T,ready,gates,table⟩:=WilsonOriginalMicroscopicGuardedNomination.calendar R F simple bliss wide d target L
  refine ⟨T,ready,gates,?_⟩
  intro r admit
  obtain ⟨j,m,dates,views⟩:=table r admit
  refine ⟨j,m,fun a=>(dates a).2,?_⟩
  intro v
  obtain ⟨Y,sources⟩:=views v
  refine ⟨Y,sources,?_⟩
  intro K before N p high seen
  let M:=fun a=>budget R F (d a) (r a) (j a) (dock (r a)^(T a)) (v a)
  let e:=coordinates R d j Y N p
  have size (a:Fin 3):((C).labels.level (d a)).coeffSize (e a) ≤ M a:=((sources a).2.1 N p (seen a)).1
  obtain ⟨A,paid,run⟩:=reports j (fun a=>(dates a).1) K before M N p high seen
  refine ⟨A,paid,fun a=>?_,run e size⟩
  exact ((paid a (e a)).1).trans (mul_le_mul_of_nonneg_left (size a) (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity))

end YM.Integration.WilsonOriginalMicroscopicGuardedEnrollment
end
