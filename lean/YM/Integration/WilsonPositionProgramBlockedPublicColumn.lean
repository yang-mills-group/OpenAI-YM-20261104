import YM.Integration.WilsonPositionProgramBlockedPublicExperiment
import YM.Integration.WilsonThermometerUnitFilingFourPool
import YM.GapsContact.Earn.Cliff
/-! Finite, quantitative original Wilson observations of a nonbare public
column on the very station that paid its reflected card. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 650000
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramBlockedPublicColumn
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C₀" => R.family
def fee (d N p j target:ℕ):ℝ:=
  let W:=(C₀).path.rep N p j
  let A:=(C₀).labels.level d
  (WilsonCapturedPrimaryCoreBill.wrapFee A (C₀).params*wraps W.p ((C₀).side j p)+
    2*WilsonCapturedPrimaryDecoder.invoice A (C₀).params d*(regulatorRun (C₀) N p (j+1))^target)*
    ((C₀).path.levels.params j).columns

def Column (r:ℝ)(j m d target:ℕ)(B:ℝ)(v:S.Field d):Prop:=
  ∃ (V:∀ k:ℕ,Vane (C₀) k)(i:ℕ)(ok:d ≤ i)(T:Spin.change S d)
    (Z:(Cells.standard (C₀)).Field d →L[ℂ] (C₀).label d),
    (V i).k=j ∧ purchaseWidth (V i)=m ∧ S.project d (Z (T.symm v))=v ∧
    Tendsto (heightV V i d) (l:Filter (ℕ×ℕ)) (𝓝 Z) ∧
    let Y:=fun u:ℕ×ℕ=>(V i).wheel.atCut u ⟨d,Nat.lt_succ_of_le ok⟩ (T.symm v)
    (∀ N p,∀ later:j<N,
      let e:=(deposited R d N p j (Y (N,p))).x
      ((C₀).labels.level d).coeffSize e  ≤  ((C₀).S.a j)^d*B*cost F d r v ∧
      ((C₀).labels.level d).coeffSize (e-recovery R d (p:=p) later.le target (Y (N,p))) ≤ 
        fee R d N p j target*(((C₀).S.a j)^d*B*cost F d r v)) ∧
    ∀ᶠ u:ℕ×ℕ in f.fuse,Cards.PaidAt (C₀).S u.1 u.2 m ((C₀).beta u.1 u.2)
      (B*cost F d r v) ((C₀).O u.1 u.2 (Y u) 0)

theorem original (simple:G.Simple)(bliss:Bliss F l Z H)
    (wide:∀ j,1 ≤ ((C₀).path.levels.budget j).supportExponent)(d target:ℕ):
    ∃t:ℕ,∀ᶠ r:ℝ in trail,∃ j m, Receipt F l r j m d (dock r^t) ∧ ∀v:S.Field d,
      Column R F (l:=l) r j m d target (dock r^t) v:=by
  obtain ⟨J,heard⟩:=Filter.eventually_atTop.mp (WilsonPositionProgramBlockedPublicExperiment.original R d simple wide target)
  obtain ⟨t,pool⟩:=WilsonThermometerUnitFilingFourPool.original F simple bliss d
  refine ⟨t,?_⟩
  have small:∀ᶠ r in trail,r*dock r^t<(C₀).S.a J:=(lake_line t).eventually (gt_mem_nhds ((C₀).S.a_pos J))
  filter_upwards [pool,small] with r data low
  obtain ⟨j,m,h⟩:=data
  have mj:J ≤ m:=le_of_not_gt fun hm=>
    (not_le_of_gt (h.front.trans low)) ((C₀).S.strictAnti.antitone hm.le)
  have jj:=mj.trans h.fore
  refine ⟨j,m,h,?_⟩
  intro v
  obtain ⟨V,i,ok,T,Y,k,into,base,lim,all⟩:=(h.budget d le_rfl).station
  have z:=all (T.symm v)
  rw [T.apply_symm_apply] at z
  obtain ⟨q,card⟩:=z
  refine ⟨V,i,ok,T,Y,k,into,(base _).trans (T.apply_symm_apply v),lim,?_,card⟩
  intro N p live x
  let w:=(V i).wheel.atCut (N,p) ⟨d,Nat.lt_succ_of_le ok⟩ (T.symm v)
  have bound:=q N p live
  have hs:=heard j jj N p live w
  let W:=(C₀).path.rep N p j;let A:=(C₀).labels.level d
  let wrap:=wraps W.p ((C₀).side j p)
  let I:=WilsonCapturedPrimaryDecoder.invoice A (C₀).params d
  let g:=regulatorRun (C₀) N p (j+1)
  let c:=((C₀).path.levels.params j).columns
  let a:=WilsonCapturedPrimaryCoreBill.wrapFee A (C₀).params
  have p₁:0 ≤ a:=mul_nonneg (Nat.cast_nonneg _) (germ_close A (C₀).params).choose_spec.1.le
  have p₂:0 ≤ wrap:=(Real.exp_pos _).le
  have p₃:0 ≤ I:=by
    unfold I WilsonCapturedPrimaryDecoder.invoice
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (Finset.sum_nonneg fun a _=>WilsonCapturedPrimaryPanel.fee_nonneg (C₀).params a d)
  have p₄:0 ≤ c:=zero_le_one.trans ((C₀).path.levels.params j).columns_ge
  have p₅:0 ≤ g:=(ActualRunKernelPackets.regulator_pos R N p (j+1) live).le
  refine ⟨bound,hs.trans ?_⟩
  change a*wrap*(c*_)+I*(2*c*_)*g^target ≤ ((a*wrap+2*I*g^target)*c)*_
  calc _ = ((a*wrap+2*I*g^target)*c)*Next.UVStress.quota (C₀) d j N p w:=by ring
       _  ≤  _:=mul_le_mul_of_nonneg_left bound (by positivity)
end YM.Integration.WilsonPositionProgramBlockedPublicColumn
end
