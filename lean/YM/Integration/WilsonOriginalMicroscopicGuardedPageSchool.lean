import YM.Integration.WilsonOriginalMicroscopicGuardedEnrollment
import YM.Integration.WilsonOriginalMicroscopicGuardedPage

/-! The common upper trial tuned to the full intrinsic page of each genuine
cutoff column, including the unit and its finite-period correction. Its
reported error is measured by the original finite experiment at that date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedPageSchool
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics
open PhysicalNext OPE.Therm Push.AbsoluteSums.Animals Next.Foundations Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap RG05Readout RG05Readout.Address
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open WilsonOriginalMicroscopicGuardedPage
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C₀" => R.family
local notation "F₀" d:max => R.family.labels.level d

def euler (d j:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a))(N p:ℕ)(a:Fin 3):(C₀).label (d a):=
  full R (d a) N p (j a) (Y a (N,p))

def Indexed (d j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)):Prop:=
  ∀K (before:∀a,j a ≤ K) N p (high:K ≤ N)(seen:∀a,j a<N),
    ∃A:∀a:Fin 3,(C₀).label (d a) ≃ₗ[ℂ] (C₀).label (d a),
    (∀a x,Arrived R (d a) (j a) K N p target (before a) high η (A a) x) ∧
    let e:=euler R d j Y N p
    let v:=fun a=>(A a).symm (e a)
    let paid:=fun a=>WilsonOriginalMicroscopicGuardedReporters.stretch R η (j a) K*((1+wrapCost R (d a) (j a))*M a)
    (∀a,let q:=deposited R (d a) N p (j a) (Y a (N,p))
        e a=page (C:=C₀) (d a) p (j a) q ∧
        (F₀ (d a)).coeffSize (v a) ≤ paid a ∧
        (F₀ (d a)).coeffSize (e a-recovery R (d a) (p:=p) (seen a).le target (Y a (N,p))) ≤
          WilsonCapturedPrimaryDecoder.invoice (F₀ (d a)) (C₀).params (d a)*
          (2*((C₀).path.levels.params (j a)).columns*M a)*(regulatorRun (C₀) N p (j a+1))^target) ∧
    ∀(o:Fin 3→Site ((C₀).side K p))(s:Finset (Fin 3)) u (prior:u ≤ K),
      (∫U,‖actualTransport (C₀) (N:=N) (gap R d N p K o v s) prior U‖ ∂scene (C₀).path N p u) ≤
        invoice R d K paid s*(C₀).path.levels.clock.forcedAllowance K

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(bliss:Bliss F l Z H)
    (wide:∀j,1 ≤ ((C₀).path.levels.budget j).supportExponent)(quote:Poetry (C₀).path.levels)
    (d:Fin 3→ℕ)(target:ℕ){η:ℝ}(ep:0<η):
    ∃T:Fin 3→ℕ,∃ready:Fin 3→Set ℝ,(∀a,ready a∈trail) ∧
    ∀r:Fin 3→ℝ,(∀a,r a∈ready a)→∃j m:Fin 3→ℕ,
      (∀a,Receipt F l (r a) (j a) (m a) (d a) (dock (r a)^(T a))) ∧
      ∀v:∀a:Fin 3,S.Field (d a),∃Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a),
        (∀a,Named R F (l:=l) (r a) (j a) (m a) (d a) target (dock (r a)^(T a)) (v a) (Y a)) ∧
        Indexed R d j target η (fun a=>budget R F (d a) (r a) (j a) (dock (r a)^(T a)) (v a)) Y:=by
  obtain ⟨L,reports⟩:=WilsonOriginalMicroscopicGuardedReporters.original R d simple shop wide quote target ep
  choose close received using fun a:Fin 3=>eventually_atTop.mp (sampled R (d a) simple wide target)
  let gates (a:Fin 3):ℕ:=max (close a) (max (R.t (d a)) ((C₀).ref (d a)))
  let floor:=max L (Finset.univ.sup gates)
  obtain ⟨T,ready,eligible,table⟩:=WilsonOriginalMicroscopicGuardedNomination.calendar R F simple bliss wide d target floor
  refine ⟨T,ready,eligible,?_⟩
  intro r entered
  obtain ⟨j,m,dates,views⟩:=table r entered
  have settled (a:Fin 3):gates a ≤ j a:=(Finset.le_sup (f:=gates) (Finset.mem_univ a)).trans ((le_max_right ..).trans (dates a).1)
  refine ⟨j,m,fun a=>(dates a).2,?_⟩
  intro v
  obtain ⟨Y,sources⟩:=views v
  refine ⟨Y,sources,?_⟩
  intro K before N p high seen
  let M:=fun a=>budget R F (d a) (r a) (j a) (dock (r a)^(T a)) (v a)
  let B:=fun a=>(1+wrapCost R (d a) (j a))*M a
  let e:=euler R d j Y N p
  let q (a:Fin 3):=deposited R (d a) N p (j a) (Y a (N,p))
  have cap (a:Fin 3):(F₀ (d a)).coeffSize (q a).x ≤ M a:=((sources a).2.1 N p (seen a)).1
  have pp (a:Fin 3):0 ≤ ((C₀).path.levels.params (j a)).columns:=zero_le_one.trans ((C₀).path.levels.params (j a)).columns_ge
  have cost (a:Fin 3):(F₀ (d a)).coeffSize (e a) ≤ B a:=by
    have localAge:= (le_max_right ..).trans (settled a)
    have priced:=wage R (d a) (p:=p) ((le_max_left ..).trans localAge) ((le_max_right ..).trans localAge)
      (seen a).le (wide _) (Y a (N,p))
    apply priced.2.trans (mul_le_mul_of_nonneg_left (cap a) _)
    have wp:0 ≤ WilsonCapturedPrimaryCoreBill.wrapFee (F₀ (d a)) (C₀).params:=
      mul_nonneg (Nat.cast_nonneg _) (germ_close (F₀ (d a)) (C₀).params).choose_spec.1.le
    have vc:=pp a
    unfold wrapCost
    positivity
  obtain ⟨A,z,run⟩:=reports j (fun a=>(le_max_left ..).trans (dates a).1) K before B N p high seen
  refine ⟨A,z,fun a=>?_,run e cost⟩
  have chart:=page_at R (d a) (p:=p) (seen a).le (Y a (N,p))
  refine ⟨chart,((z a (e a)).1).trans (mul_le_mul_of_nonneg_left (cost a) (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity)),?_⟩
  have read:=received a (j a) ((le_max_left ..).trans (settled a)) N p (seen a) (Y a (N,p))
  have g:=ActualRunKernelPackets.regulator_pos R N p (j a+1) (seen a)
  apply read.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg g.le _)
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_left (cap a) (mul_nonneg (by norm_num) (pp a))
  · unfold WilsonCapturedPrimaryDecoder.invoice
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (Finset.sum_nonneg fun z _=>WilsonCapturedPrimaryPanel.fee_nonneg (C₀).params z (d a))

end YM.Integration.WilsonOriginalMicroscopicGuardedPageSchool
end
