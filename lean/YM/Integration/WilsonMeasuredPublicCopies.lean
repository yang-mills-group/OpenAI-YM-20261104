import YM.Integration.WilsonMeasuredPublicSlots

/-! Translated representatives, joint smooth readings and reflected tests of the same finite public roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicCopies
open Source Push Function Filter Set MeasureTheory Finset Table Lattice Wilson RG Cells Extraction Spec Climb OPE
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicSlots
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  {F : Final R.family f S} {l : Ultrafilter (ℕ×ℕ)} {I : Type} [Fintype I]
  {d : I → ℕ} {v : ∀ i, S.Field (d i)} {s B : I→ℝ}
  (L : ∀i, Slot F l (d i) (v i) (s i) (B i))

def amount (i : I) := B i * GapsContact.Ascent.cost F (d i) (s i) (v i)

def field (q : ℕ×ℕ) (i:I) (o : Site (R.family.side q.1 q.2)) :=
  R.family.O q.1 q.2 ((L i).arm.source q) o

omit [Fintype I] in
theorem at_site (q : ℕ×ℕ) (i:I) (o : Site (R.family.side q.1 q.2)) :
    field L q i o = R.family.O q.1 q.2
      (((L i).calendar (L i).station).wheel.atCut q ⟨d i,Nat.lt_succ_of_le (L i).admissible⟩
        ((L i).frame.symm (v i))) 0 ∘ translate o := by
  unfold field
  rw [← (L i).actual]
  funext U
  simp only [Family.O,TransferData.cylinder,Source.initial,Function.comp_apply,Pi.smul_apply,
    Source.SectionData.places_trans,zero_add]

/-- One ordered regulator gate precedes every position, placement and test chamber. -/
theorem copies :
    ∀ᶠ q : ℕ×ℕ in f.fuse,∃ live : ∀i, (L i).m ≤ q.1,
      ∀ (T : Tiling (R.family.side q.1 q.2)) (c:I→T.Cell) (o:I→Site (R.family.side q.1 q.2)),
        (∀i, Cells.span R.family.S (live i) q.2 ∣ T.side.val) →
        (∀i, o i∈T.margin (c i) (3*Cells.span R.family.S (live i) q.2)) →
        Seam G (R.family.side q.1 q.2) (R.family.beta q.1 q.2) →
        ∃ h : I → Config G (R.family.side q.1 q.2)→ℂ,∀i,
          T.copy (c i) (h i)=field L q i (o i) ∧ Interior (T.chamber 0) (h i) ∧
          T.rootTest (R.family.beta q.1 q.2) (h i) ≤ amount (F:=F) (B:=B) (s:=s) (v:=v) i := by
  filter_upwards [eventually_all.mpr fun i=>(L i).reflected] with q cards
  refine ⟨fun i=>(cards i).live,?_⟩
  intro T c o divides places seam
  choose h attached room paid using fun i=>(cards i).any T (divides i) (places i) seam
  refine ⟨h,fun i=>⟨?_,room i,paid i⟩⟩
  rw [attached]
  funext U
  simp only [field,Family.O,TransferData.cylinder,Source.initial,Function.comp_apply,Pi.smul_apply,
    Source.SectionData.places_trans,zero_add]

section Smooth
variable {n : ℕ} {grade : Caps n} {names : ∀i,S.Field (grade i)} {height rent : Fin n→ℝ}

theorem smooth (horder : (l:Filter (ℕ×ℕ))≤f.fuse)
    (slots : ∀i,Slot F l (grade i) (names i) (height i) (rent i)) (t : Test n) :
    Tendsto (fun q : ℕ×ℕ=>Order.smears R.family q.1 q.2
      (fun i=>⟨grade i,(slots i).arm.source q⟩) t) (l:Filter _) (𝓝 (t.applyTo (fun x=>S.classMoment S grade x names))) := by
  exact WilsonThermometerUnitFilingFourSquare.measured F horder
    (fun i _=>(slots i).arm) (fun _=>false) t
end Smooth

end YM.Integration.WilsonMeasuredPublicCopies
