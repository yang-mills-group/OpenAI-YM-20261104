import YM.Integration.WilsonThermometerWeakSeatedExterior
import YM.Integration.WilsonThermometerWeakWardExterior

/-! The original Ward footprints clear once the physical displacements do. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakRosterMargins
open Set Function Lattice Wilson RG Source Labels Next.Extract PhysicalNext.Repeat.Legato Push
open WilsonOffsetReportingProducts (Avoids)
open WilsonThermometerWeakSeatedExterior (Seats padding)
open WilsonPositionPhysicalCellTest (Sites)
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G}
local notation "C" => R.family
local notation "S" => R.family.S

def extent {d:ℕ}{F:Labels.Frame G d}(E:SectionData F):ℕ:=E.stencil.sup Laurent.size

theorem clears {n:Side}{d:ℕ}{F:Labels.Frame G d}(E:SectionData F)(z o:Site n)(k:ℕ)
    (far:k+extent E<separation z o):
    (↑(E.footprint z):Set (Site n))⊆Mark.Outer k o:=by
  intro x live
  obtain ⟨q,member,rfl⟩:=Finset.mem_image.mp live
  have small:separation z (wrap n q+z)≤extent E:=
    (by simpa [FreeResolvent.Affine.View.addr,add_comm] using FreeResolvent.Affine.View.separation_view z q :
      separation z (wrap n q+z)≤Laurent.size q).trans (Finset.le_sup (f:=Laurent.size) member)
  have tri:=separation_triangle z (wrap n q+z) o
  change k<separation (wrap n q+z) o
  omega

def invoice {n:ℕ} {J:Type}[Fintype J](V:∀d,SectionData ((C).labels.level d))(d:Fin n→ℕ)
    (e:J→ℕ)(rad:ℕ→ℕ):ℕ:=
  Finset.univ.sup (fun i=>rad (d i)) +
    max (Finset.univ.sup (fun i=>max (extent ((C).localSection (d i))) (extent (V (d i)))))
      (Finset.univ.sup (fun i=>extent ((C).localSection (e i))))

theorem physical {n:ℕ}{J:Type}[Fintype J](V:∀d,SectionData ((C).labels.level d))
    (d:Fin n→ℕ)(e:J→ℕ)(rad:ℕ→ℕ)(s:Finset (Fin n))
    (j m N p:ℕ)(k:J→ℕ)(start:j+padding (R:=R) J s+1 ≤ m)(deep:∀i,j+padding (R:=R) J s+1≤k i)
    (o:J→Site ((C).side N p))(z:Sites R (N,p) n)(x:(s ⊕ J) → Lattice.Cover)
    (left:∀i:s,wrap ((C).side N p) (x (.inl i))=z i)(right:∀i:J,wrap ((C).side N p) (x (.inr i))=o i)
    (q:s ⊕ J→E4)(err:∀i (a:Axis),|(S).gridPoint N (x i) a-q i a|≤(S).a N)
    (small:(S).a N≤(S).a j)(width:(invoice V d e rad:ℝ)*(S).a N<(S).a j)
    (gap:∀i i',i≠i'→∃a:Axis,3*(S).a j≤|q i a-q i' a|)
    (period:∀i i' (a:Axis),2*(|q i a-q i' a|+3*(S).a j)<((S).period p).val):
    Avoids («C» := (C)) V rad (fun i:s=>d i) (fun i=>z i) ∧
    (∀(i:s)(t:J),(↑(((C).localSection (e t)).footprint (o t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (z i)) ∧
    Seats (R:=R) (m:=m) s k z o:=by
  let D:=fun i a=>(S).gridPoint N (x i) a
  have close (i i') (a:Axis):
      |D i a-D i' a| ≤ |q i a-q i' a|+2*(S).a N ∧
      |q i a-q i' a| ≤ |D i a-D i' a|+2*(S).a N:=by
    have e₁:=err i a;have e₂:=err i' a
    change |D i a-q i a|≤_ at e₁;change |D i' a-q i' a|≤_ at e₂
    have rev₁:=e₁;have rev₂:=e₂;rw [abs_sub_comm] at rev₁ rev₂
    have one:=abs_sub_le (D i a) (q i a) (D i' a)
    have two:=abs_sub_le (q i a) (q i' a) (D i' a)
    have three:=abs_sub_le (q i a) (D i a) (q i' a)
    have four:=abs_sub_le (D i a) (D i' a) (q i' a)
    constructor <;> linarith
  have split (i i') (no:i≠i'):∃a:Axis,(S).a j≤|D i a-D i' a|:=by
    obtain ⟨a,h⟩:=gap i i' no
    exact ⟨a,by linarith only [h,(close i i' a).2,small]⟩
  have unwound (i i') (a:Axis):2*(|D i a-D i' a|+(S).a j)<((S).period p).val:=by
    linarith only [period i i' a,(close i i' a).1,small]
  have dist (i i') (no:i≠i'):
      invoice V d e rad<separation (wrap ((C).side N p) (x i)) (wrap ((C).side N p) (x i')):=by
    apply WilsonThermometerWeakWardExterior.grid («S» := (S)) N p _ _ _
    · intro a;rw [mul_comm _ ((S).a N), (S).span_side]
      exact (by linarith only [unwound i i' a,(S).a_pos j] : 2*|D i a-D i' a|<((S).period p).val)
    · obtain ⟨a,h⟩:=split i i' no;exact ⟨a,width.trans_le h⟩
  have lead (i:Fin n):rad (d i)≤Finset.univ.sup (fun i=>rad (d i)):=Finset.le_sup (f:=fun i=>rad (d i)) (Finset.mem_univ i)
  have loud (i:Fin n):max (extent ((C).localSection (d i))) (extent (V (d i))) ≤
      Finset.univ.sup (fun j=>max (extent ((C).localSection (d j))) (extent (V (d j)))):=Finset.le_sup (f:=fun j=>max (extent ((C).localSection (d j))) (extent (V (d j)))) (Finset.mem_univ i)
  have side (t:J):extent ((C).localSection (e t))≤Finset.univ.sup (fun j=>extent ((C).localSection (e j))):=Finset.le_sup (f:=fun j=>extent ((C).localSection (e j))) (Finset.mem_univ t)
  refine ⟨?_,?_,j,start,deep,x,left,right,split,?_⟩
  · intro i l different
    have h:=dist (.inl l) (.inl i) (by simpa only [ne_eq,Sum.inl.injEq] using different.symm)
    rw [left,left] at h;unfold invoice at h
    have c:=lead i;have f:=loud l
    constructor
    · apply clears; dsimp only; omega
    · apply clears; dsimp only; omega
  · intro i t
    have h:=dist (.inr t) (.inl i) (by simp)
    rw [right,left] at h;unfold invoice at h
    have c:=lead i;have f:=side t
    apply clears;omega
  · intro i i' a
    rw [mul_comm _ ((S).a j),(S).span_side];exact unwound i i' a

end YM.Integration.WilsonThermometerWeakRosterMargins
end
