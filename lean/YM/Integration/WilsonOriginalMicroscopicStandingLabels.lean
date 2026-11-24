import YM.Integration.WilsonOriginalMicroscopicGuardedNomination

/-! A prescribed public receipt selects one original cutoff column for every
public input before the numerical extraction order is chosen. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicStandingLabels
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C" => R.family

def Press (r:ℝ)(j m d:ℕ)(B:ℝ)(Y:S.Field d→ℕ×ℕ→(C).label d):Prop:=
  (∃ (V:∀k:ℕ,Vane (C) k)(i:ℕ)(ok:d ≤ i)(T:Spin.change S d)(Z:(Cells.standard (C)).Field d→L[ℂ](C).label d),
    (V i).k=j ∧ purchaseWidth (V i)=m ∧ (∀x,S.project d (Z x)=T x) ∧
    Tendsto (heightV V i d) (l:Filter (ℕ×ℕ)) (𝓝 Z) ∧
    ∀v u,Y v u=(V i).wheel.atCut u ⟨d,Nat.lt_succ_of_le ok⟩ (T.symm v)) ∧
  ∀v, (∀N p,j<N→((C).labels.level d).coeffSize (deposited R d N p j (Y v (N,p))).x
      ≤budget R F d r j B v) ∧
    ∀ᶠ u:ℕ×ℕ in f.fuse,Cards.PaidAt (C).S u.1 u.2 m ((C).beta u.1 u.2)
      (B*cost F d r v) ((C).O u.1 u.2 (Y v u) 0)

theorem before {r B:ℝ}{j m d:ℕ}(standing:Receipt F l r j m d B):
    ∃Y:S.Field d→ℕ×ℕ→(C).label d,Press R F (l:=l) r j m d B Y:=by
  obtain ⟨V,i,ok,T,Z,site,reach,physical,tends,paid⟩:=(standing.budget d le_rfl).station
  refine ⟨fun v u=>(V i).wheel.atCut u ⟨d,Nat.lt_succ_of_le ok⟩ (T.symm v),
    ⟨V,i,ok,T,Z,site,reach,physical,tends,fun _ _=>rfl⟩,?_⟩
  intro v
  have invoice:=paid (T.symm v)
  rw [T.apply_symm_apply] at invoice
  exact invoice

theorem named (simple:G.Simple)(wide:∀j,1≤((C).path.levels.budget j).supportExponent)(d target:ℕ):
    ∀ᶠ j:ℕ in atTop,∀r m B (Y:S.Field d→ℕ×ℕ→(C).label d),
      Press R F (l:=l) r j m d B Y→∀v,Named R F (l:=l) r j m d target B v (Y v):=by
  filter_upwards [WilsonPositionProgramBlockedPublicExperiment.original R d simple wide target] with j heard
  intro r m B Y standing v
  obtain ⟨⟨V,i,ok,T,Z,site,reach,physical,tends,source⟩,sold⟩:=standing
  obtain ⟨q,card⟩:=sold v
  refine ⟨⟨V,i,ok,T,Z,site,reach,(physical _).trans (T.apply_symm_apply _),tends,source v⟩,?_,card⟩
  intro N p live x
  let w:=Y v (N,p)
  have bound:=q N p live
  have hs:=heard N p live w
  let W:=(C).path.rep N p j; let A:=(C).labels.level d
  let wrap:=wraps W.p ((C).side j p)
  let I:=WilsonCapturedPrimaryDecoder.invoice A (C).params d
  let g:=regulatorRun (C) N p (j+1)
  let c:=((C).path.levels.params j).columns
  let a:=WilsonCapturedPrimaryCoreBill.wrapFee A (C).params
  have p₁:0≤a:=mul_nonneg (Nat.cast_nonneg _) (germ_close A (C).params).choose_spec.1.le
  have p₂:0≤wrap:=(Real.exp_pos _).le
  have p₃:0≤I:=by
    unfold I WilsonCapturedPrimaryDecoder.invoice
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (Finset.sum_nonneg fun a _=>WilsonCapturedPrimaryPanel.fee_nonneg (C).params a d)
  have p₄:0≤c:=zero_le_one.trans ((C).path.levels.params j).columns_ge
  have p₅:0≤g:=(ActualRunKernelPackets.regulator_pos R N p (j+1) live).le
  refine ⟨bound,hs.trans ?_⟩
  change a*wrap*(c*_)+I*(2*c*_)*g^target≤((a*wrap+2*I*g^target)*c)*_
  calc _=((a*wrap+2*I*g^target)*c)*Next.UVStress.quota (C) d j N p w:=by ring
       _≤_:=mul_le_mul_of_nonneg_left bound (by positivity)

end YM.Integration.WilsonOriginalMicroscopicStandingLabels
end
