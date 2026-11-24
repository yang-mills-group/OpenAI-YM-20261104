import YM.Integration.WilsonMeasuredPublicEntranceProfileMesh
import YM.Integration.WilsonMeasuredPublicEntranceProfileSites
import YM.Integration.WilsonSeparatedPrefixGridGround
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation

/-! Every occupied periodic cell of a joint smooth test has one genuine separated lift.
The finite menu determining the physical reporting date is independent of the number
of coordinates of the test. The earlier date is common to the two physical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomePlacement
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Extraction Table Spec Trace.Pilot
open Trace.Physical.GermGraph PhysicalNext.Repeat.Legato RG16 RG16.Literal
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReceivedChronologicalFixedRoseVariation (cells charged)
open WilsonMeasuredPublicEntranceScreen (Ground)
open Climb Maxwell Maxwell.Free Trace.Terrace Trace.Physical Trace.Physical.Germ GapsContact
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][Nonempty I]

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T:ℕ}{δ:ℝ}(d:I→Fin (D+1))(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {n:ℕ}[Nonempty (Fin n)](φ:Test n)(h:ℕ):
    ∃apron:ℕ,∀floor:ℕ,∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},
      (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∃j:ℕ,floor≤j ∧ j+2≤f ∧ ∀ s : ℝ, r ≤ s → s ≤ outer z h r → ∀N per,f≤N→∀a:cells R φ s (f,per),
        Ground R N per j f apron a.val ∧
        Pairwise fun i k=>(R.family.path.levels.budget f).B^2<separation (a.val i) (a.val k):=by
  classical
  obtain ⟨L,η,lp,ep,shape⟩:=WilsonSeparatedPrefixCellProfile.shape φ
  have positive:0<L+1:=by linarith
  obtain ⟨apron,grounds⟩:=WilsonSeparatedPrefixGridGround.original F simple bliss slow D T h d books
    (L:=L+1) positive (η:=η/2) (half_pos ep)
  refine ⟨apron,?_⟩
  intro floor
  have mesh:=WilsonMeasuredPublicEntranceProfileMesh.original (I:=I) F simple D T n books
    (t:=min 1 (η/4)) (lt_min zero_lt_one (by positivity))
  filter_upwards [grounds floor,mesh,self_mem_nhdsWithin (a:=(0:ℝ))] with r available small rp
  intro ρ span near f
  obtain ⟨j,late,height,ground⟩:=available ρ span near
  refine ⟨j,late,height,?_⟩
  have rpos:0<r:=rp
  have size:=small ρ near
  have bound:4*(n:ℝ)*R.family.S.a f≤r:=size.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 (η/4)) rpos.le)
  have apart:4*(n:ℝ)*R.family.S.a f≤η/4*r:=size.trans (mul_le_mul_of_nonneg_right (min_le_right ..) rpos.le)
  intro s lower upper N per live a
  obtain ⟨q,fixed,admission⟩:=WilsonMeasuredPublicEntranceProfileSites.lifted R φ (per:=per) (rpos.trans_le lower) shape (bound.trans lower) (apart.trans (mul_le_mul_of_nonneg_left lower (by positivity)))
  obtain ⟨inside,separated⟩:=admission a.val (charged R φ s (f,per) a)
  have receipt:Ground R N per j f apron a.val:=by
    rw [←fixed a.val]
    exact (ground (Fin n) N per live (q a.val)
      (fun i=>(inside i).trans (mul_le_mul_of_nonneg_left upper positive.le)) (fun i k distinct=>(mul_le_mul_of_nonneg_left lower (half_pos ep).le).trans (separated distinct))).1
  refine ⟨receipt,?_⟩
  intro i k ne
  have distance:=receipt.2.1 i k ne
  have eq:(R.family.path.rep N per f).p=R.family.path.levels.budget f:=(R.makes.wilson.represents N per f live).vac
  rw [eq] at distance
  exact distance

end YM.Integration.WilsonOriginalGeneralRosterHomePlacement
end
