import YM.Integration.WilsonThermometerWeakWardPair
import YM.Push.FREE_RESOLVENT.Views

/-! The actual displaced arm is an admissible spectator of the finite Haar
equation on every separated, unwrapped pair of fine sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardExterior
open Set Function Lattice RG Wilson Labels Source Push Next.Extract PhysicalNext.Repeat.Legato
open Cells
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

def stencil (d:ℕ):ℕ:=((C).localSection d).stencil.sup Laurent.size

theorem support (d:ℕ) {n:Side} (o:Site n) {z:Site n} (inside:z∈((C).localSection d).footprint o):
    separation o z ≤ stencil R d:=by
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp inside
  exact (by simpa [FreeResolvent.Affine.View.addr,add_comm] using FreeResolvent.Affine.View.separation_view o v :
    separation o (wrap n v+o) ≤ Laurent.size v).trans (Finset.le_sup (f:=Laurent.size) hv)

theorem original (d N p:ℕ) (x:(C).label d) (w:ℂ) (o z:Site ((C).side N p)) (r:ℕ)
    (far:r+stencil R d<separation z o):
    LocalOn (Mark.Outer r o) (fun U=>w*(C).O N p x z U):=by
  intro U V same
  apply congr_arg (fun a:ℂ=>w*a)
  apply (C).localO N p d x z U V
  have incl {i:Site ((C).side N p)} (inside:i∈((C).localSection d).footprint z): i∈Mark.Outer r o:=by
    have small:=support R d z inside
    have joined:=separation_triangle z i o
    change r<separation i o
    omega
  exact fun i left right=>same i (incl left) (incl right)

theorem grid {S:Schedule} (N p:ℕ) (x y:Cover) (r:ℕ)
    (wraps:∀i:Axis,2*|S.gridPoint N x i-S.gridPoint N y i|<((S.side N p).val:ℝ)*S.a N)
    (far:∃i:Axis,(r:ℝ)*S.a N < |S.gridPoint N x i-S.gridPoint N y i|):
    r<separation (wrap (S.side N p) x) (wrap (S.side N p) y):=by
  let n:=S.side N p
  have eqv:wrap (S.side N p) x-wrap (S.side N p) y=wrap n (x-y):=by
    rw [map_sub]
  have canonical:lift (wrap (S.side N p) x-wrap (S.side N p) y)=x-y:=by
    apply lift_eq_iff.mpr;refine ⟨eqv,?_⟩
    intro i
    have room:=wraps i
    have priced:S.gridPoint N x i-S.gridPoint N y i=S.a N*((x-y) i:ℤ):=by
      change S.a N*(x i:ℝ)-S.a N*(y i:ℝ)=_
      simp only [Pi.sub_apply,Int.cast_sub,mul_sub]
    rw [priced,abs_mul,abs_of_pos (S.a_pos N)] at room
    have h : 2*|(((x-y) i:ℤ):ℝ)|<(n.val:ℝ):=
      (mul_lt_mul_iff_left₀ (S.a_pos N)).mp (by linarith only [room])
    have bounds:=abs_le.mp (le_refl |(((x-y) i:ℤ):ℝ)|)
    constructor
    · exact_mod_cast (show -(n.val:ℝ)<2*(((x-y) i:ℤ):ℝ) from by linarith)
    · exact_mod_cast (show 2*(((x-y) i:ℤ):ℝ)≤(n.val:ℝ) from by linarith)
  obtain ⟨i,edge⟩:=far
  have price:S.gridPoint N x i-S.gridPoint N y i=S.a N*(((x-y) i:ℤ):ℝ):=by
    change S.a N*(x i:ℝ)-S.a N*(y i:ℝ)=_
    simp only [Pi.sub_apply,Int.cast_sub,mul_sub]
  rw [price,abs_mul,abs_of_pos (S.a_pos N),mul_comm (r:ℝ)] at edge
  have strict: (r:ℝ) < |(((x-y) i:ℤ):ℝ)|:=(mul_lt_mul_iff_right₀ (S.a_pos N)).mp edge
  have atCoord:=component_le (wrap (S.side N p) x-wrap (S.side N p) y) i
  rw [canonical] at atCoord
  apply lt_of_lt_of_le _ atCoord
  have h:(r:ℤ) < |((x-y) i:ℤ)|:=by exact_mod_cast strict
  exact_mod_cast (show (r:ℤ)<(((x-y) i).natAbs:ℤ) by simpa only [Int.natCast_natAbs] using h)

end YM.Integration.WilsonThermometerWeakWardExterior
end
