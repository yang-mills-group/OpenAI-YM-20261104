import YM.Integration.WilsonPositionProgramBlockedPublicColumn

/-! The three physical measurements can use different radii and different
reporting dates. Their every-cutoff labels are the actual wheels at those
dates. Each comes with its original public projection, cutoff extraction,
calibrated coordinate bound and signed recovery error. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedNomination
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C" => R.family

def budget (d:ℕ)(r:ℝ)(j:ℕ)(B:ℝ)(v:S.Field d):ℝ:=((C).S.a j)^d*B*cost F d r v

def Named (r:ℝ)(j m d target:ℕ)(B:ℝ)(v:S.Field d)(Y:ℕ×ℕ→(C).label d):Prop:=
  (∃ (V:∀k:ℕ,Vane (C) k)(i:ℕ)(ok:d ≤ i)(T:Spin.change S d)(A:(Cells.standard (C)).Field d →L[ℂ] (C).label d),
    (V i).k=j ∧ purchaseWidth (V i)=m ∧ S.project d (A (T.symm v))=v ∧
    Tendsto (heightV V i d) (l:Filter (ℕ×ℕ)) (𝓝 A) ∧
    ∀u:ℕ×ℕ,Y u=(V i).wheel.atCut u ⟨d,Nat.lt_succ_of_le ok⟩ (T.symm v)) ∧
  (∀N p,∀seen:j<N,
    let e:=(deposited R d N p j (Y (N,p))).x
    ((C).labels.level d).coeffSize e ≤ budget R F d r j B v ∧
      ((C).labels.level d).coeffSize (e-recovery R d (p:=p) seen.le target (Y (N,p))) ≤
        WilsonPositionProgramBlockedPublicColumn.fee R d N p j target*budget R F d r j B v) ∧
  ∀ᶠ u:ℕ×ℕ in f.fuse,Cards.PaidAt (C).S u.1 u.2 m ((C).beta u.1 u.2)
      (B*cost F d r v) ((C).O u.1 u.2 (Y u) 0)

theorem named {d j m target:ℕ}{r B:ℝ}{v:S.Field d}
    (c:WilsonPositionProgramBlockedPublicColumn.Column R F (l:=l) r j m d target B v):
    ∃Y:ℕ×ℕ→(C).label d,Named R F (l:=l) r j m d target B v Y:=by
  obtain ⟨V,i,ok,T,A,date,width,sectionEq,limit,earned,paid⟩:=c
  exact ⟨_,⟨V,i,ok,T,A,date,width,sectionEq,limit,fun _=>rfl⟩,earned,paid⟩

theorem calendar (simple:G.Simple)(bliss:Bliss F l Z H)(wide:∀j,1 ≤ ((C).path.levels.budget j).supportExponent)
    (d:Fin 3→ℕ)(target floor:ℕ):
    ∃ T:Fin 3→ℕ,∃ready:Fin 3→Set ℝ,(∀a,ready a∈trail) ∧
    ∀ r:Fin 3→ℝ,(∀a,r a∈ready a)→∃j m:Fin 3→ℕ,
      (∀a,floor ≤ j a ∧ Receipt F l (r a) (j a) (m a) (d a) (dock (r a)^(T a))) ∧
      ∀v:∀a:Fin 3,S.Field (d a),∃Y:∀a:Fin 3,ℕ×ℕ→(C).label (d a),
        ∀a,Named R F (l:=l) (r a) (j a) (m a) (d a) target (dock (r a)^(T a)) (v a) (Y a):=by
  choose T offers using fun a:Fin 3=>WilsonPositionProgramBlockedPublicColumn.original R F simple bliss wide (d a) target
  let ready (a:Fin 3):Set ℝ:={r | ∃j m:ℕ,floor ≤ j ∧ Receipt F l r j m (d a) (dock r^(T a)) ∧
      ∀v:S.Field (d a),WilsonPositionProgramBlockedPublicColumn.Column R F (l:=l) r j m (d a) target (dock r^(T a)) v}
  have gate (a:Fin 3):ready a∈trail:=by
    have small:∀ᶠ r:ℝ in trail,r*dock r^(T a)<(C).S.a floor:=(lake_line (T a)).eventually (gt_mem_nhds ((C).S.a_pos floor))
    filter_upwards [offers a,small] with r offer low
    obtain ⟨j,m,standing,all⟩:=offer
    have paid:floor ≤ m:=le_of_not_gt fun hm=>(not_le_of_gt (standing.front.trans low)) ((C).S.strictAnti.antitone hm.le)
    exact ⟨j,m,paid.trans standing.fore,standing,all⟩
  refine ⟨T,ready,gate,?_⟩
  intro r eligible
  choose j m large standing bank using eligible
  refine ⟨j,m,fun a=>⟨large a,standing a⟩,?_⟩
  intro v
  choose Y chosen using fun a=>named R F (bank a (v a))
  exact ⟨Y,chosen⟩

end YM.Integration.WilsonOriginalMicroscopicGuardedNomination
end
