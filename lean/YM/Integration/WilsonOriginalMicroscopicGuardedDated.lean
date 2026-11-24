import YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool

/-! The original fitted reporters and their full earlier deposits on prescribed
public dates, using the already selected cutoff labels on those dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedDated
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
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalMicroscopicGuardedGridSchool
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C₀" => R.family
local notation "F₀" d:max => R.family.labels.level d

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((C₀).path.levels.budget j).supportExponent)(quote:Poetry (C₀).path.levels)
    (d:Fin 3→ℕ)(target:ℕ){η:ℝ}(ep:0<η):
    ∃L:ℕ,∀j:Fin 3→ℕ,(∀a,L ≤ j a)→∀(M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)),
      (∀a N p,j a<N→(F₀ (d a)).coeffSize (deposited R (d a) N p (j a) (Y a (N,p))).x ≤ M a)→
      Finished R d j target η M Y:=by
  obtain ⟨L,reports⟩:=WilsonOriginalMicroscopicGuardedReporters.original R d simple shop wide quote target ep
  choose close received using fun a:Fin 3=>eventually_atTop.mp (sampled R (d a) simple wide target)
  choose h govern using fun a:Fin 3=>eventually_atTop.mp (WilsonAddressedRestartedGrid.original R (d a) simple)
  let gates (a:Fin 3):ℕ:=max (close a) (max (R.t (d a)) ((C₀).ref (d a)))
  let floor:=max L (Finset.univ.sup gates)
  refine ⟨max floor (Finset.univ.sup h),?_⟩
  intro j late M Y cash
  have paid (a:Fin 3):floor ≤ j a:=(le_max_left ..).trans (late a)
  have settled (a:Fin 3):gates a ≤ j a:=(Finset.le_sup (f:=gates) (Finset.mem_univ a)).trans ((le_max_right ..).trans (paid a))
  constructor
  · intro K before N p high seen
    let B:=fun a=>(1+wrapCost R (d a) (j a))*M a
    let e:=euler R d j Y N p
    let q (a:Fin 3):=deposited R (d a) N p (j a) (Y a (N,p))
    have cap (a:Fin 3):(F₀ (d a)).coeffSize (q a).x ≤ M a:=cash a N p (seen a)
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
    obtain ⟨A,z,run⟩:=reports j (fun a=>(le_max_left ..).trans (paid a)) K before B N p high seen
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
  · intro f n N p onGrid live A arrived a
    let x:=((C₀).factory (d a) N p).terminal.symm (Y a (N,p))
    have age:h a≤j a:=(Finset.le_sup (f:=h) (Finset.mem_univ a)).trans ((le_max_right ..).trans (late a))
    have paint:=govern a (j a) age N p f n (Nat.le_add_right_of_le (onGrid a)) live target η (A a) x
    have chart:euler R d j Y N p a=page (C:=C₀) (d a) p (j a) (((C₀).factory (d a) N p).entries (j a) x):=
      page_at R (d a) (p:=p) ((Nat.le_add_right_of_le (onGrid a)).trans live) (Y a (N,p))
    dsimp only at paint
    rw [←chart] at paint
    exact paint (arrived a _) (onGrid a)

end YM.Integration.WilsonOriginalMicroscopicGuardedDated
end
