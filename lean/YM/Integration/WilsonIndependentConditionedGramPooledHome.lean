import YM.Integration.WilsonIndependentConditionedGramRawHome
import YM.Integration.WilsonMovingForkSlotDate
import YM.Integration.WilsonReflectedMixedLocatedSchool

/-! Cash the unprojected trial-home income of the recorded physical slots
on their common reporter before the independent planting cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramPooledHome
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open RG16 RG16.Literal OPE Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonMovingForkOpticalBook (reporter station_le)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonIndependentConditionedBankRawUnits (home)
open WilsonIndependentConditionedGramRawHome (fixed)
open WilsonMovingForkSlotDate (slot)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I]
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

theorem on_book (D T:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(ρ:I→{s:ℝ // 0<s ∧ s<δ})
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)(M:I→ℝ)(E:I→ℕ)
    (paid:Paid F D T d books field M E ρ (reporter F books ρ))
    (flag:I→Bool)(η:ℝ)(small:η ≤ 1)(α:I→ℂ)(dose:∀i,‖α i‖ ≤ 1)(c:I→ℝ)(colour:∀i,0 ≤ c i):
    let f:=reporter F books ρ
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i=>station F (L i) (flag i)
    let w:=fun i=>fee F (L i) (flag i) (field i (ρ i) (flag i))
    let H₀:=fun i=>home R (d i).val (j i) f η (α i) (w i)
    (∀i,0 ≤ H₀ i ∧ H₀ i ≤ M i*fixed R (d i).val*(β f)^(E i)) ∧
    ∀s:Finset I,(∏i∈s,(1+H₀ i*c i)) ≤
      (∏i∈s,(1+M i*fixed R (d i).val*c i))*(β f)^(∑i∈s,E i):=by
  intro f L j w H₀
  have income (i:I):0 ≤ H₀ i ∧ H₀ i ≤ M i*fixed R (d i).val*(β f)^(E i):=by
    have budget:=paid i (flag i)
    refine ⟨WilsonIndependentConditionedGramRawHome.nonnegative R _ _ _ _ _ budget.1,?_⟩
    apply WilsonIndependentConditionedGramRawHome.charged R (dose i) budget.1
      (station_le F books ρ i (d i) (flag i)) small
    exact (le_max_right ..).trans budget.2.2
  exact ⟨income,fun s=>WilsonIndependentConditionedGramRawHome.face R s E H₀
    (fun i=>M i*fixed R (d i).val) c (fun i=>(income i).1) colour (fun i=>(income i).2)⟩

variable [Nonempty I]

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
    (∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    ∀(field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
      (M:I→ℝ)(E:I→ℕ),Paid F D T d books field M E ρ f →
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i=>station F (L i) false
    let w:=fun i=>fee F (L i) false (field i (ρ i) false)
    ∀(η:ℝ), 0 ≤ η → η ≤ 1 → ∀(α:I→ℂ),(∀i,‖α i‖ ≤ 1) →
    let H₀:=fun i=>home R (d i).val (j i) f η (α i) (w i)
    ∀(c:I→ℝ),(∀i,0 ≤ c i) →
    (∀i,a (j i)/a f ≤ (β f)^(2*T+11+2*h) ∧
      H₀ i ≤ M i*fixed R (d i).val*(β f)^(E i+(2*T+11+2*h)*((d i).val+1))) ∧
    ∀s:Finset I,(∏i∈s,(1+H₀ i*c i)) ≤ (∏i∈s,(1+M i*fixed R (d i).val*c i))*
      (β f)^(∑i∈s,(E i+(2*T+11+2*h)*((d i).val+1))):=by
  classical
  filter_upwards [WilsonMovingForkSlotDate.original F simple bliss slow D T h 0 d books] with r located
  intro ρ span near f field M E paid L j w η low small α dose H₀ c colour
  let v:=fun i=>field i (ρ i) false
  have positions:=located ρ span near v
  have reaches (i:I):a (j i)/a f ≤ (β f)^(2*T+11+2*h):=by
    change a ((books (ρ i)).stock.j)/a f ≤ _
    simpa only [(WilsonMovingForkSlotDate.source F (books (ρ i)) (d i) (v i)).1] using (positions i).2.2.1
  have income (i:I):H₀ i ≤ M i*fixed R (d i).val*(β f)^(E i+(2*T+11+2*h)*((d i).val+1)):=
    WilsonIndependentConditionedGramRawHome.leaf R (dose i) (paid i false).1
      (paid i false).2.1 (reaches i) low small
  exact ⟨fun i=>⟨reaches i,income i⟩,fun s=>WilsonIndependentConditionedGramRawHome.face R s _
    H₀ _ c (fun i=>WilsonIndependentConditionedGramRawHome.nonnegative R _ _ _ _ _ (paid i false).1) colour income⟩

end YM.Integration.WilsonIndependentConditionedGramPooledHome
