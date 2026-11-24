import YM.QuadraticLocal.Earn.Passport
import YM.Integration.FVA1Physical.Marked.QuayLampSpatial

/-! Choose a lifted tour of each physical field stencil before fixing the
period and the positions of the fields. Its original length, including
excursions that wrap or coincide after projection, pays the CP5 passport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Lattice Finset RG Push.AbsoluteSums QuadraticLocal.Earn
open Next.Foundations Source YM.Integration.FVA1Physical.Round2.Curvature
open RGComparison.Core16.Spool
open scoped Classical

private def tour : List Cover → Walk
  | [] => []
  | y :: ys => (route 0 y 1 ++ Lattice.reverse (route 0 y 1)) ++ tour ys

private theorem tour_visits {n:Side} (o:Site n) (ys:List Cover) :
    ∀ y∈ys, wrap n y+o ∈ Paths.native o (tour ys) := by
  induction ys with
  | nil => simp
  | cons a ys ih =>
    intro y hy
    have endpt : stop o (route 0 a 1)=wrap n a+o := by
      simpa only [map_zero,add_zero,add_comm] using Work.E03.stop_route o 0 a
    rw [tour,Cable.Native.combine,stop_append,reverse_stop]
    rcases List.mem_cons.mp hy with rfl|h
    · apply mem_union_left
      rw [Cable.Native.combine]
      exact mem_union_left _ (endpt ▸ Cable.Native.tip o (route 0 y 1))
    · exact mem_union_right _ (ih y h)

variable {G:Gauge} {d:ℕ} {I:Type} {n:Side}

/-- This number is fixed for a cover field, before selecting the period,
placement, test, or the other members of the marker roster. -/
def stencilHeight (a:CoverLabel G d) : ℕ :=
  (tour (localSection G a.1.val).stencil.toList).length

def stencilPassport (a:I → CoverLabel G d) (o:I → Site n) : Passport n I where
  origin := o
  support i := insert (o i) ((localSection G (a i).1.val).footprint (o i))
  wire i := tour (localSection G (a i).1.val).stencil.toList
  height i := stencilHeight (a i)
  born _ := mem_insert_self ..
  visits i := by
    intro x hx
    rcases mem_insert.mp hx with rfl|h
    · exact Cable.Native.first ..
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
      exact tour_visits (o i) _ y (Finset.mem_toList.mpr hy)
  room _ := le_rfl

theorem stencil_field_local [Fintype I] (a:I → CoverLabel G d) (o:I → Site n) (i:I) :
    LocalOn ((stencilPassport a o).support i)
      (Light (Marked.freshLamps a i) n (o i)) := by
  intro U V h
  apply (localSection G (a i).1.val).placed_local (o i) (Pi.single (a i).2 1) U V
  apply agrees_mono h
  exact Finset.coe_subset.mpr (Finset.subset_insert ..)

theorem stencil_coarse {c:Side} (g:Ratio c n) (a:I → CoverLabel G d) (o:I → Site n) (i:I) :
    ((stencilPassport a o).coarser g).support i =
      (insert (o i) ((localSection G (a i).1.val).footprint (o i))).image g.parent ∧
    ((stencilPassport a o).coarser g).height i = Cable.mass g (stencilHeight (a i)) := ⟨rfl,rfl⟩

end YM.Integration.FVA1Physical.Round2.CP5
