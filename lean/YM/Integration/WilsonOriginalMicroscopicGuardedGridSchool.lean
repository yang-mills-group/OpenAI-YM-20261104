import YM.Integration.WilsonOriginalMicroscopicGuardedPageSchool
import YM.Integration.WilsonAddressedRestartedGrid

/-! Each elected public full page keeps its centered calibration and its own
physical grid address when all upper sources reach the same date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool
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
open WilsonOriginalMicroscopicGuardedPageSchool WilsonAddressedRestartedColumn
open WilsonPositionProgramOriginalBlockedTrial RG05Readout.Records
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C₀" => R.family
local notation "F₀" d:max => R.family.labels.level d

def Placed (d j:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a))
    (f n N p:ℕ)(live:f+n≤N)(A:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a)):Prop:=
  ∀a,let x:=((C₀).factory (d a) N p).terminal.symm (Y a (N,p))
    let v:=(A a).symm (euler R d j Y N p a)
    let B:=hike (C₀) (f+n) f rate*((1+4*stock (C₀) (f+n))*((C₀).labels.level (d a)).coeffSize v)
    ∀o:Site ((C₀).side f p),∃z:store (C₀) (d a) p f,
      WilsonAddressedRestartedFiled.Filed R (d a) N p f o
        (track R (d a) N p (f+n) (numerator R (d a) N p (f+n) 0 v) f-calValues (C:=C₀) (d a) N p f x) B z ∧
      z.density o ((C₀).localSection (d a)) ((C₀).path.rep N p f)=
        WilsonAddressedRestartedGrid.difference R (d a) N p f n live o v x

def Finished (d j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)):Prop:=
  Indexed R d j target η M Y ∧
  ∀f n N p (part:∀a,j a≤f)(live:f+n≤N)(A:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a)),
    (∀a x,Arrived R (d a) (j a) (f+n) N p target (Nat.le_add_right_of_le (part a)) live η (A a) x)→
    Placed R d j Y f n N p live A

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(bliss:Bliss F l Z H)
    (wide:∀j,1 ≤ ((C₀).path.levels.budget j).supportExponent)(quote:Poetry (C₀).path.levels)
    (d:Fin 3→ℕ)(target floor:ℕ){η:ℝ}(ep:0<η):
    ∃T:Fin 3→ℕ,∃ready:Fin 3→Set ℝ,(∀a,ready a∈trail) ∧
    ∀r:Fin 3→ℝ,(∀a,r a∈ready a)→∃j m:Fin 3→ℕ,
      (∀a,floor≤j a ∧ Receipt F l (r a) (j a) (m a) (d a) (dock (r a)^(T a))) ∧
      ∀v:∀a:Fin 3,S.Field (d a),∃Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a),
        (∀a,Named R F (l:=l) (r a) (j a) (m a) (d a) target (dock (r a)^(T a)) (v a) (Y a)) ∧
        Finished R d j target η (fun a=>budget R F (d a) (r a) (j a) (dock (r a)^(T a)) (v a)) Y:=by
  obtain ⟨T,ready,early,publish⟩:=WilsonOriginalMicroscopicGuardedPageSchool.original R F simple shop bliss wide quote d target ep
  choose h govern using fun a:Fin 3=>eventually_atTop.mp (WilsonAddressedRestartedGrid.original R (d a) simple)
  let cutoff:=max floor (Finset.univ.sup h)
  let before (a:Fin 3):Set ℝ:={r|r∈ready a ∧ r*dock r^(T a)<(C₀).S.a cutoff}
  have small(a:Fin 3):before a∈trail:=by
    have near:∀ᶠ r:ℝ in trail,r*dock r^(T a)<(C₀).S.a cutoff:=(lake_line (T a)).eventually (gt_mem_nhds ((C₀).S.a_pos cutoff))
    filter_upwards [early a,near] with r paid close
    exact ⟨paid,close⟩
  refine ⟨T,before,small,?_⟩
  intro r okay
  obtain ⟨j,m,receipts,people⟩:=publish r (fun a=>(okay a).1)
  have late(a:Fin 3):cutoff≤j a:=by
    have bound:cutoff ≤ m a:=le_of_not_gt fun hm=> (not_le_of_gt ((receipts a).front.trans (okay a).2)) ((C₀).S.strictAnti.antitone hm.le)
    exact bound.trans (receipts a).fore
  refine ⟨j,m,fun a=>⟨(le_max_left ..).trans (late a),receipts a⟩,?_⟩
  intro v
  obtain ⟨Y,named,indexed⟩:=people v
  refine ⟨Y,named,indexed,?_⟩
  intro f n N p onGrid live A arrived a
  let x:=((C₀).factory (d a) N p).terminal.symm (Y a (N,p))
  have age:h a≤j a:=(Finset.le_sup (f:=h) (Finset.mem_univ a)).trans ((le_max_right ..).trans (late a))
  have paint:=govern a (j a) age N p f n (Nat.le_add_right_of_le (onGrid a)) live target η (A a) x
  have chart:euler R d j Y N p a=page (C:=C₀) (d a) p (j a) (((C₀).factory (d a) N p).entries (j a) x):=
    page_at R (d a) (p:=p) ((Nat.le_add_right_of_le (onGrid a)).trans live) (Y a (N,p))
  dsimp only at paint
  rw [←chart] at paint
  exact paint (arrived a _) (onGrid a)

end YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool
end
