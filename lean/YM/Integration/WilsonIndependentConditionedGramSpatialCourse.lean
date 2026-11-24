import YM.Integration.WilsonIndependentConditionedGramSpatialHost
import YM.Integration.WilsonIndependentConditionedGramSpatialAperture
import YM.Integration.WilsonIndependentConditionedGramPooledHome

/-! One nearest spatial reporting station and the already booked optical
reporter and cutoff, on the same physical run before the UV and period limits. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramSpatialCourse
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open RG16 RG16.Literal OPE Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonIndependentConditionedGramSpatialHost (date)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

structure Page (r:ℝ)(m f K t U p:ℕ)(ε:ℝ):Prop where
  positive : 0 < r
  live : 0 < m
  covers : a m ≤ r
  previous : r < a (m-1)
  before : m ≤ f
  higher : f < K
  root_one : 1 ≤ r/a m
  root_block : r/a m < ((R.family.S.block (m-1)).val:ℝ)
  slow_block : ((R.family.S.block (m-1)).val:ℝ) ≤ 1+Real.log (Real.log (β (m-1)))
  root_power : (1+r/a m)^p ≤ (1+((R.family.S.block (m-1)).val:ℝ))^p
  block_power : (1+((R.family.S.block (m-1)).val:ℝ))^p ≤ (β f)^ε
  optical : r/a f ≤ (β f)^U
  coupled : 0 < thermal R f ∧ thermal R f ≤ 1
  recess : (thermal R f)^(2*U) ≤ a f/a m ∧ a f/a m ≤ 1
  mesh : a K/a m=(a K/a f)*(a f/a m)
  lower : (thermal R f)^(2*(t+1)+2*U) ≤ a K/a m
  upper : a K/a m ≤ (thermal R f)^(2*t)

variable {R}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][Nonempty I]

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h t p:ℕ)(d:I→Fin (D+1)){δ ε:ℝ}(positive:0 < ε)
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
    (∃i,(ρ i).val=r) →
    let m:=date R simple r; let f:=reporter F books ρ; let K:=berth R t f
    Page R r m f K t (2*T+11+2*h) p ε ∧
    ∀i,max (books (ρ i)).stock.j (books (ρ i)).W.k ≤ f ∧ (ρ i).val/a f ≤ (β f)^(2*T+11+2*h):=by
  classical
  have spans:=WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books
  obtain ⟨floor,opened⟩:=eventually_atTop.mp (WilsonIndependentConditionedBankBerth.acquired R simple slow t)
  filter_upwards [spans,WilsonIndependentConditionedGramSpatialHost.root R simple slow p positive,
    (WilsonIndependentConditionedGramSpatialHost.late R simple).eventually_ge_atTop floor]
    with r seen shape grown
  intro ρ margins anchor m f K
  have measured:=seen ρ margins anchor
  have first:m ≤ f:=WilsonIndependentConditionedGramSpatialHost.first R simple shape.1 measured.1
  have sell:=opened f (grown.trans first)
  let U:=2*T+11+2*h
  obtain ⟨index,pin⟩:=anchor
  have ok:r ≤ (β f)^U*a f:=pin ▸ (measured.2 index).2
  obtain ⟨pos,live,size,prev,one,last,slowBlock,weight⟩:=shape
  have earn:=WilsonIndependentConditionedGramSpatialAperture.window R first size ok sell.2.2.2.1 sell.2.2.2.2
  refine ⟨⟨pos,live,size,prev,first,sell.1,one,last,slowBlock,(weight f first).1,(weight f first).2,
    (div_le_iff₀ (R.family.S.a_pos f)).2 ok,⟨sell.2.1,sell.2.2.1⟩,⟨earn.1,earn.2.1⟩,
    WilsonIndependentConditionedGramSpatialAperture.factor R m f K,earn.2.2.1,earn.2.2.2⟩,?_⟩
  exact fun i=>⟨(measured.2 i).1,(div_le_iff₀ (R.family.S.a_pos f)).2 (measured.2 i).2⟩

end YM.Integration.WilsonIndependentConditionedGramSpatialCourse
