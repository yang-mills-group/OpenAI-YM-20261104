import YM.MS.Port.Spire
import YM.Lattice.Subdivision
/-!
# Reciprocal lifts and period path. Strict-periodic kernel switch later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Function Filter Set Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{T n:Side}{x y z u:QP}{s p: Cover}
-- pitch = per spacing
abbrev walk (n:Side) := Tone.Mesh.hz n
abbrev ψstep (n:Side):= tier / ( n.val:ℝ )
lemma ψpp (n:Side):0<ψstep n:= div_pos rising ( Bloch.side_pos n )
lemma η_walk (n:Side)(x:Cover): walk n x= whole ( ψstep n ) x:= by unfold walk Tone.Mesh.hz; funext i; change ((n.val:ℝ)⁻¹ *((2*π)*(x i:ℝ))) = (2*π/(n.val:ℝ)) * ( x i:ℝ ); ring
abbrev νt (n:Side) : ℝ:= ((n.val:ℝ)^4)⁻¹
lemma ν_pos (n:Side): 0< νt n:= inv_pos.mpr ( pow_pos ( Bloch.side_pos n ) _ )
lemma ℝwalk (n:Side)(x:Cover): (n.val:ℝ) • walk n x= rep x:= Tone.Mesh.position n x
lemma natural (n:Side)(x:Cover): walk n ( n.val • x )=rep x:= by rw [ map_nsmul, ← ℝwalk n x, Nat.cast_smul_eq_nsmul ]
lemma τ_amount (n:Side): amountB (ψstep n)=νt n := by unfold amountB ψstep νt tier; field_simp [Real.pi_ne_zero]
def congrQ (p q:QP): Prop:= ∃ x:Cover,p=q+rep x
namespace congrQ
lemma normal (x:QP): congrQ x x:=⟨0,by simp⟩
lemma trans (h:congrQ x y)(e:congrQ y z): congrQ x z:= by obtain ⟨a,rfl⟩:= h; obtain ⟨v,rfl⟩:=e; exact ⟨ v+a,by rw [map_add]; abel⟩
lemma sym (h:congrQ x y): congrQ y x:= by obtain ⟨a,rfl⟩:= h; exact ⟨ -a,by rw [map_neg]; abel⟩
lemma plus (h:congrQ x y)(he:congrQ z u): congrQ (x+z) (y+u):= by obtain ⟨a,rfl⟩:=h; obtain ⟨b,rfl⟩:=he; exact ⟨ a+b,by rw [map_add]; abel⟩
lemma opp (h:congrQ x y): congrQ (-x) (-y):=by obtain ⟨a,rfl⟩:=h; exact ⟨-a,by rw [map_neg]; abel⟩
lemma out (h: wrap n s= wrap n p): congrQ ( walk n s ) ( walk n p ):= by obtain ⟨c,rfl⟩:= Bloch.cover_of_eq p s h.symm; exact ⟨ c,by rw [ map_add, natural ] ⟩
end congrQ
abbrev wrapZ (n:Side)(p:Site n):= walk n (Lattice.lift p)
abbrev Coord (x:Site n):= wrapZ n x
lemma ξ_rel (x:Cover): congrQ (walk n x) (Coord (wrap n x)):= congrQ.out (wrap_lift _) |>.sym
lemma ξ_add (x y:Site n): congrQ (Coord x + Coord y) ( Coord (x+y) ) := by unfold Coord wrapZ; rw [← map_add]; apply congrQ.out; simp
lemma ξ_neg (x:Site n): congrQ (-Coord x) (Coord (-x)):= by unfold Coord wrapZ; rw [← map_neg]; apply congrQ.out; simp
lemma ξ_zero (n:Side): Coord (0:Site n) =0:= by have hp : Lattice.lift (0:Site n)=0:=(by ext; simp [Lattice.lift]); unfold Coord wrapZ; rw [ hp,map_zero ]
-- cell phase.Signal
lemma pin_pay (x:Cover) {p q:QP}(h:congrQ p q): bill p (Tone.embed x)=bill q (Tone.embed x):= by obtain ⟨a,rfl⟩:=h; rw [payadd, reciprocal, mul_one ]
lemma dual_cell (x:Site n)(p:Cover): bill (Tone.embed p) (Coord x)= Bloch.cell x (wrap n p):= by
    rw [ Tone.rights,Tone.castNative,Bloch.cell_wrap ]; have he:(fun i:Axis=>( Coord x i:ℂ ))= Bloch.mon x:= by funext i; unfold Coord wrapZ walk Tone.Mesh.hz rep Tone.embed Bloch.mon Laurent.reciprocal; change ((((n.val:ℝ)⁻¹*(2*π*(Lattice.lift x i:ℝ)):ℝ)):ℂ) = _; push_cast; rfl
    rw [ he ]; -- spacing parentheses inspect
abbrev η_fix (v:Site (2:Side)) := Coord v
lemma bill_walk (x p:Cover): bill (Tone.embed p) ( walk n x )= Bloch.cell (wrap n x) (wrap n p):= by rw [rights,pin_pay p (ξ_rel x),rights,dual_cell]
end YM.MS.Orbit
