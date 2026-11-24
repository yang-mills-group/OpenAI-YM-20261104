import YM.Integration.WilsonMatrixOriginalDeckPrescriptionSeries

/-! The triangular transfer acts on all of the independently filed Wilson gauge functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionFields
open PhysicalNext.Repeat.Legato Finset Lattice Wilson RG MS MS.Menus MS.Local.Physical WilsonMatrixOriginalDeckPrescription
open scoped Classical BigOperators Matrix
variable {G:Gauge}{B:Deck G} (R:Run G) (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

def slice (a:I):Glyph B a.size≃{b:I // b.size≤a.size} where
  toFun j:=⟨resized j ((Nat.le_of_lt_succ j.1.isLt).trans (Nat.le_of_lt_succ a.1.isLt)),Nat.le_of_lt_succ j.1.isLt⟩
  invFun j:=resized j.val j.property
  left_inv _:=rfl
  right_inv _:=rfl

def raw (N p:ℕ)(o:Site (R.family.side N p))(U:Config G (R.family.side N p))(a:I):ℂ:=
  R.family.O N p (WilsonMacroscopicRichOriginalPortfolio.label R N p a) o U

def field (μ:ℝ)(k N p:ℕ)(o:Site (R.family.side N p))(U:Config G (R.family.side N p))(a:I):ℂ:=
  WilsonMacroscopicRichOriginalPortfolio.observation R Q N p (WilsonMatrixOriginalDeckRawPanel.name h a) μ k o U

theorem observed (μ:ℝ)(k N p:ℕ)(o:Site (R.family.side N p))(U:Config G (R.family.side N p))(a:I):
    field R Q h μ k N p o U a=∑b:I,fees Q h μ k b a*raw R h N p o U b:=by
  let e:=slice (B:=B) h a
  let value:=fun b:I=>fees Q h μ k b a*raw R h N p o U b
  let s:=Finset.univ.filter fun b:I=>b.size≤a.size
  have sliceSum:(∑b∈s,value b)=∑b:{j:I // j.size≤a.size},value b.val:=
    Finset.sum_subtype s (by intro x;simp [s]) value
  have extend:(∑b∈s,value b)=∑b:I,value b:=by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b _ outside
    have no:¬b.size≤a.size:=by simpa [s] using outside
    dsimp only [value];rw [fees,dif_neg no,zero_mul]
  calc
    field R Q h μ k N p o U a=∑j:Glyph B a.size,value (e j).val:=by
      unfold field WilsonMacroscopicRichOriginalPortfolio.observation WilsonMatrixOriginalDeckRawPanel.name
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [value]
      rw [fees,dif_pos (e j).property];rfl
    _ = ∑b:{j:I // j.size≤a.size},value b.val:=e.sum_comp fun b=>value b.val
    _ = _:=sliceSum.symm.trans extend

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionFields
