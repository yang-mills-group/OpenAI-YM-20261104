import YM.Integration.WilsonOriginalGeneralRosterHomeUnion
import YM.Integration.WilsonIndependentConditionedGramSpatialCourse
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

/-! Each stock sees its own first physical mesh on the union's one reporting
berth. The Page retains the common K when the test is dilated at a distant home. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomePage
open Function Filter Finset Set Lattice RG Wilson Source Labels Extraction Table Spec Trace.Pilot
open PhysicalNext.Repeat.Legato Climb
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth arrival)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonIndependentConditionedGramSpatialCourse (Page)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

theorem ordered (simple:G.Simple)(s:ℕ):Monotone (berth R s):=by
  intro i j ij
  have reach:=arrival R s j
  unfold berth
  apply Nat.find_min'
  refine ⟨ij.trans_lt reach.1,?_⟩
  exact ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (zero_lt_one.trans (R.family.path.levels.fits.delayed i)).le
    (WilsonReflectedOpticalStock.monotone R simple ij) s) (R.family.S.a_pos _).le).trans reach.2).trans
    (R.family.S.strictAnti.antitone ij)

variable {R}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][Nonempty I]

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h power p:ℕ)(d:I→Fin (D+1)){δ ε:ℝ}(ep:0<ε)
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    let K:=berth R power f
    ∀i,let scale:=(ρ i).val;let q:=max (books (ρ i)).stock.j (books (ρ i)).W.k
      berth R 5 q ≤ f ∧ a f/scale ≤ (wilson z scale)^2 ∧
      Page R scale (date R simple scale) f K power (2*T+11+2*h) p ε:=by
  classical
  have singletonMesh:=WilsonOriginalTwoFlatPublicMixedMesh.original (I:=Unit) F simple bliss slow D T 0
    (fun _=>0) books
  obtain ⟨limit,lp,asked⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp
    ((WilsonIndependentConditionedGramSpatialHost.root R simple slow p ep).and singletonMesh)
  have narrow:∀ᶠr in trail,outer z h r ≤ limit:=(longer F simple bliss h).eventually
    ((eventually_le_nhds lp).filter_mono nhdsWithin_le_nhds)
  obtain ⟨floor,opened⟩:=eventually_atTop.mp (WilsonIndependentConditionedBankBerth.acquired R simple slow power)
  filter_upwards [narrow,WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books,
    (WilsonIndependentConditionedGramSpatialHost.late R simple).eventually_ge_atTop floor] with r low spans grown
  intro ρ within anchor f K i scale q
  have seen:=spans ρ within anchor
  have positive:0<r:=by
    obtain ⟨idx,near⟩:=anchor
    exact near ▸ (ρ idx).property.1
  have root:=WilsonIndependentConditionedGramSpatialHost.first R simple positive seen.1
  have sold:=opened f (grown.trans root)
  have ready:=asked (Set.mem_Ioc.mpr ⟨(ρ i).property.1,((within i).2).trans low⟩)
  have single:=ready.2 (fun _:Unit=>ρ i) (fun _=>⟨le_rfl,by simp [outer]⟩) ⟨(),rfl⟩
  have fine:a (berth R 5 q)/scale ≤ (wilson z scale)^2:=by simpa [q,scale] using single.1
  have before:berth R 5 q ≤ f:=ordered R simple 5
    (le_sup (f:=fun j=>max (books (ρ j)).stock.j (books (ρ j)).W.k) (mem_univ i))
  have mesh:a f/scale ≤ (wilson z scale)^2:=(div_le_div_of_nonneg_right
    (R.family.S.strictAnti.antitone before) (ρ i).property.1.le).trans fine
  have first:=WilsonIndependentConditionedGramSpatialHost.first R simple (ρ i).property.1 (seen.1.trans (within i).1)
  obtain ⟨pos,live,size,prev,one,last,old,weight⟩:=ready.1
  have reach:= (seen.2 i).2
  have bill:=WilsonIndependentConditionedGramSpatialAperture.window R first size reach sold.2.2.2.1 sold.2.2.2.2
  exact ⟨before,mesh,⟨pos,live,size,prev,first,sold.1,one,last,old,(weight f first).1,(weight f first).2,
    (div_le_iff₀ (R.family.S.a_pos f)).2 reach,⟨sold.2.1,sold.2.2.1⟩,⟨bill.1,bill.2.1⟩,
    WilsonIndependentConditionedGramSpatialAperture.factor R _ f K,bill.2.2.1,bill.2.2.2⟩⟩

end YM.Integration.WilsonOriginalGeneralRosterHomePage
end
