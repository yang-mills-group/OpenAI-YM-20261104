import YM.Integration.WilsonOriginalCensusPositiveDose

/-! Restore just the deterministic zero-grade choices in the preselected positive basis menu. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusUnitMenu
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open PhysicalNext.Repeat.Legato WilsonThermometerDeclaredSeeds
open WilsonIndependentCollarOrbitalBasisPayment
open WilsonOriginalCensusPositiveSites (names pick part positive Group)
open WilsonOriginalCensusPositiveDose (reduced)
open WilsonOriginalCensusUnitDose (enrolled)
open scoped BigOperators Classical

variable {G:Gauge}{n:ℕ}(R:Run G)(k:Fin n→ℕ)(s:(Replicum.Bud (Fin n)).Mode)

def place (j:s.val)(pos:0<k j):(part k s).val:=
  let c:Group k:=(pick k).symm ⟨j.val,pos⟩
  have home:names k c=j.val:=congrArg Subtype.val ((pick k).apply_symm_apply _)
  ⟨c,mem_filter.mpr ⟨mem_univ _,home ▸ j.property⟩⟩

theorem home (j:s.val)(pos:0<k j):names k (place k s j pos)=j.val:=
  congrArg Subtype.val ((pick k).apply_symm_apply _)

def fixed (b:Choices R (k ∘ names k) (part k s).val)(j:s.val):Choice R k j:=
  if pos:0<k j then
    cast (congrArg (fun l=>Choice R k l) (home k s j pos)) (b (place k s j pos))
  else .inl ()

theorem funded (b:Choices R (k ∘ names k) (part k s).val):
    ∀j:s.val,k j=0 → fixed R k s b j=.inl ():=by
  intro j zero
  simp [fixed,zero]

private theorem paid (b:Choices R (k ∘ names k) (part k s).val)(j:s.val)(pos:0<k j):
    HEq (fixed R k s b j) (b (place k s j pos)):=by
  rw [fixed,dif_pos pos]
  exact cast_heq _ _

theorem crop (b:Choices R (k ∘ names k) (part k s).val):reduced R k s (fixed R k s b)=b:=by
  funext l
  let j:s.val:=⟨names k l,(mem_filter.mp l.property).2⟩
  have pos:0<k j:=positive k l
  have address:place k s j pos=l:=Subtype.ext ((names k).injective (home k s j pos))
  have shifted:HEq (b (place k s j pos)) (b l):=by rw [address]
  have seen:reduced R k s (fixed R k s b) l=fixed R k s b j:=by
    simp only [reduced,enrolled,dif_pos j.property,j]
  rw [seen]
  exact eq_of_heq ((paid R k s b j pos).trans shifted)

theorem restored (a:Choices R k s.val)(units:∀j:s.val,k j=0 → a j=.inl ()):
    fixed R k s (reduced R k s a)=a:=by
  funext j
  by_cases pos:0<k j
  · let p:=place k s j pos
    let l:s.val:=⟨names k p,(mem_filter.mp p.property).2⟩
    have address:l=j:=Subtype.ext (home k s j pos)
    have seen:reduced R k s a p=a l:=by simp only [reduced,enrolled,dif_pos l.property,l]
    have moved:HEq (a l) (a j):=by rw [address]
    exact eq_of_heq ((paid R k s (reduced R k s a) j pos).trans (seen.heq.trans moved))
  · rw [fixed,dif_neg pos,units j (by omega)]

def menu:{a:Choices R k s.val // ∀j:s.val,k j=0 → a j=.inl ()} ≃ Choices R (k ∘ names k) (part k s).val where
  toFun a:=reduced R k s a
  invFun b:=⟨fixed R k s b,funded R k s b⟩
  left_inv a:=Subtype.ext (restored R k s a a.property)
  right_inv b:=crop R k s b

theorem enrollment (a:Choices R k s.val)(j:Group k):
    enrolled R k s.val a (names k j)=
      enrolled R (k ∘ names k) (part k s).val (reduced R k s a) j:=by
  by_cases hj:names k j∈s.val
  · have inside:j∈(part k s).val:=mem_filter.mpr ⟨mem_univ _,hj⟩
    rw [enrolled,dif_pos hj,enrolled,dif_pos inside,reduced,enrolled,dif_pos hj]
  · have outside:j∉(part k s).val:=fun hx=>hj (mem_filter.mp hx).2
    simp only [enrolled,dif_neg hj,dif_neg outside]
    rfl

end YM.Integration.WilsonOriginalCensusUnitMenu
