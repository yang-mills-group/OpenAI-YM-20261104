import YM.Integration.WilsonOriginalGeneralRosterHomeReturn

/-! The full product, the same-name two-copy tests at the original stock
radii, and every preannounced external test spend one physical bank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeMenu
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Climb Maxwell Maxwell.Free Trace.Terrace GapsContact
open OPE PhysMS MS MS.Land FVA2 FVA2.Register Next.Extract GapsContact.Seams GapsContact.Ascent
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Issued)
open WilsonOriginalGeneralRosterUnionFile (Sold)
open WilsonOriginalGeneralRosterUnion (Row request need)
open WilsonOriginalGeneralRosterResponse (difference Phase)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG16 RG16.Literal RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool){ρ:I→{s:ℝ//0<s ∧ s<δ}}
local notation "C" => R.family
open WilsonOriginalGeneralRosterUnionReturn (Returned)

def menu {B:Type}(main:Row I)(pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)(outside:B→Row I):
    Unit⊕(Fin main.size⊕B)→Row I
  | .inl _=>main
  | .inr (.inl i)=>⟨2,by decide,fun _=>main.stock i,p i,pair i⟩
  | .inr (.inr b)=>outside b

def dilation {B:Type}(main:Row I)(ρ:I→ℝ)(r:ℝ)(home:B→Option I):Unit⊕(Fin main.size⊕B)→ℝ
  | .inl _=>r
  | .inr (.inl i)=>ρ (main.stock i)
  | .inr (.inr b)=>(home b).elim r ρ

omit [Fintype I] [Nonempty I] in
theorem housed {B:Type}(main:Row I)(ρ:I→ℝ)(r top:ℝ)(home:B→Option I)(up:r≤top)
    (legal:∀i,r≤ρ i ∧ ρ i≤top)(v:Unit⊕(Fin main.size⊕B)):
    r≤dilation main ρ r home v ∧ dilation main ρ r home v≤top:=by
  rcases v with v|v
  · exact ⟨le_rfl,up⟩
  · rcases v with p|b
    · exact legal (main.stock p)
    · cases hb:home b with
      | none=>simpa only [dilation,hb,Option.elim_none] using And.intro (le_refl r) up
      | some i=>simpa only [dilation,hb,Option.elim_some] using legal i

def Sold {B:Type}[Fintype B](main:Row I)(pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)
    (outside:B→Row I)(home:B→Option I)(M:I→ℝ)(E:I→ℕ)(h t:ℕ):Prop:=
  let rows:=menu main pair p outside
  ∀target:ℕ,
    let e:=need d E rows
    let pwr:=univ.sup e+1
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let tuition:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀ lo : ℕ, ∃ (base j₀ ear₀ j₁ ear₁ : ℕ), lo ≤ base ∧ base ≤ j₀ ∧ j₀ ≤ ear₀ ∧ ear₀ < ear₁ ∧ j₁ ≤ ear₁ ∧ Stop (C) 0 j₀ ear₀ ∧ Stop (C) 0 j₁ ear₁ ∧
    ∀ᶠr in trail,
      ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      let K:=berth R reserve f
      ∃A:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val),
      (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f) ∧
      ∀w:Unit⊕(Fin main.size⊕B),∃j:ℕ,ear₁≤j ∧ j+2≤f ∧ ∀mode branch:I→Bool,
        Returned F books field (ρ:=ρ) (rows w).stock (mode ∘ (rows w).stock) (branch ∘ (rows w).stock) A M E tuition power target t
          f K base j ear₀ ear₁ (request E (rows w)) (rows w).desired (rows w).test (dilation main (fun i=>(ρ i).val) r home w)

theorem original (grant:WilsonOriginalGeneralRosterHomeReturn.Register F books h t d field)
    {B:Type}[Fintype B](main:Row I)(pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)(outside:B→Row I)(home:B→Option I):
    ∃(M:I→ℝ)(E:I→ℕ),(∀i,1≤M i) ∧ Sold F books field main pair p outside home M E h t:=by
  classical
  obtain ⟨M,E,first,market⟩:=grant
  refine ⟨M,E,first,?_⟩
  unfold Sold
  intro rows target eps degree reserve tuition power lo
  obtain ⟨base,u₀,v₀,u₁,v₁,near,b₀,s₀,later,s₁,old,far,campus⟩:=market _ rows target lo
  refine ⟨base,u₀,v₀,u₁,v₁,near,b₀,s₀,later,s₁,old,far,?_⟩
  filter_upwards [campus] with r ready
  intro ρ span anchor f K
  obtain ⟨A,measured,tab⟩:=ready ρ span anchor
  refine ⟨A,measured,?_⟩
  intro w
  obtain ⟨gate,older,age,served⟩:=tab w
  have up:= (span (Classical.arbitrary I)).1.trans (span _).2
  have house:=housed main (fun i=>(ρ i).val) r _ home up span w
  exact ⟨gate,older,age,fun mode branch=>served _ house.1 house.2 (mode ∘ (rows w).stock) (branch ∘ (rows w).stock)⟩

theorem four (grant:WilsonOriginalGeneralRosterHomeReturn.Register F books h t d field)
    {B:Type}[Fintype B](arm:Fin 4→I)(φ:Test 4)(accuracy:ℕ)(pair:Fin 4→Test 2)(p:Fin 4→ℕ)(outside:B→Row I)(home:B→Option I):
    let main:Row I:=⟨4,by decide,arm,accuracy,φ⟩
    ∃(M:I→ℝ)(E:I→ℕ),(∀i,1≤M i) ∧ Sold F books field main pair p outside home M E h t:=by
  intro main
  exact original F books field grant main pair p outside home

end YM.Integration.WilsonOriginalGeneralRosterHomeMenu
end
