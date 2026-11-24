import YM.Integration.WilsonConditionalTaylorLabels
import YM.Push.FREE_RESOLVENT.Torus

/-! Each actual colored basis lamp occurs as an original occupied singleton.
Its native finite stencil has the same radius at every site, on every periodic
lattice, including a displacement crossing a torus seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetLampRoster
open Function Lattice RG Wilson Labels Next.Foundations RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels
open scoped Classical BigOperators
variable {G:Gauge} {d:ℕ}

def row (i:((frames G).level d).Index):Roster G := [⟨d,i⟩]
def slot (i:((frames G).level d).Index) : Fin (row i).length := ⟨0,by simp [row]⟩
def card (i:((frames G).level d).Index) : Finset (Fin (row i).length) := {slot i}
def line (i:((frames G).level d).Index) : ↥(card i)→Lamp G :=fun t=>lamps (row i) t.val

theorem literal (i:((frames G).level d).Index) {n:Side} (y:Site n) (U:Config G n) :
    tally (line i) (fun _=>y) U=(localSection G d).places (Pi.single i 1) y U :=by
  let s:↥(card i):=⟨slot i,by simp [card]⟩
  change (∏ t:↥(card i),Light (line i t) n y U)=_
  rw [Finset.prod_eq_single s]
  · rfl
  · intro b _ diff
    exact (diff (Subtype.ext (Finset.mem_singleton.mp b.property))).elim
  · exact fun hn=>(hn (Finset.mem_univ _)).elim

def radius (G:Gauge) (d:ℕ) := (localSection G d).stencil.sup (fun x:Cover=>Laurent.size x)

theorem collar (i:((frames G).level d).Index) {n:Side} (y:Site n) (w:ℕ) (hw:0<w)
    (t:Slice (line i)) :
    separation y (legs (line i) (fun _=>y) t).1 ≤ radius G d*w :=by
  have s : t.1.val=slot i:=Finset.mem_singleton.mp t.1.property
  obtain ⟨⟨b,hb⟩,⟨u,v⟩⟩:=t
  have hi:b=slot i:=s
  subst b
  let x₀:Cover:=u.val
  have mem:x₀∈(localSection G d).stencil:=u.property
  have cap:Laurent.size x₀ ≤ radius G d:=Finset.le_sup (f:=fun v:Cover=>Laurent.size v) mem
  change separation y (wrap n x₀ + y) ≤ _
  rw [separation_comm,separation,add_sub_cancel_right]
  apply le_trans _ (Nat.le_mul_of_pos_right (radius G d) hw)
  have small:pdist (wrap n x₀) ≤ Laurent.size (lift (wrap n x₀)):=by
    apply Finset.sup_le
    intro a _
    apply Finset.single_le_sum (f:=fun a:Axis=>(lift (wrap n x₀) a).natAbs) (fun _ _=>Nat.zero_le _)
    exact Finset.mem_univ a
  exact small.trans ((FreeResolvent.wrap_size n x₀).trans cap)

end YM.Integration.WilsonOffsetLampRoster
