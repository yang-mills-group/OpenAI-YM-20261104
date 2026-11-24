import YM.Cells.Packing
import YM.Integration.WilsonPositionOriginalDiagnosticRightReading

/-! A common legal Wilson reflection cut for each submitted moving position
and every lower physical field stencil in a prescribed finite horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticHalfSpace
open Finset Filter Set Lattice Wilson Cells
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "S"=>R.family.S

def radius (h:ℕ)(a:Axis):ℕ:=∑d∈range (h+1),∑k∈(R.family.localSection d).stencil,(k a).natAbs

private theorem paid {h d:ℕ}(a:Axis){k:Cover}(inside:d≤h)(leg:k∈(R.family.localSection d).stencil) :
    (k a).natAbs≤radius R h a:=by
  exact (single_le_sum (s:=(R.family.localSection d).stencil) (f:=fun u=>(u a).natAbs)
    (fun _ _=>Nat.zero_le _) leg).trans
    (single_le_sum (s:=range (h+1)) (f:=fun e=>∑u∈(R.family.localSection e).stencil,(u a).natAbs)
      (fun _ _=>Nat.zero_le _) (mem_range_succ_iff.mpr inside))

def sheet (N per:ℕ)(a:Axis)(o:Site (R.family.side N per))(b:ℕ):Cut (R.family.side N per) where
  half:=Cells.half S N per
  even:=Cells.original S N per
  kind:=.site
  pos:=a
  baseLine:=o a-(b:Per (R.family.side N per))

/-- Arbitrary spatial offsets and all time offsets in the indicated strip
are legal with one real reflection, simultaneously for every field stencil. -/
theorem places {h b w N per d:ℕ}(a:Axis)(o:Site (R.family.side N per))(e:Cover)(inside:d≤h)
    (under:radius R h a+w<b)(high:b+w+radius R h a<(Cells.half S N per).val)(pos:(e a).natAbs≤w):
    ↑((R.family.localSection d).footprint (wrap (R.family.side N per) e+o)) ⊆
      (sheet R N per a o b).sector:=by
  intro q hq
  change q∈(R.family.localSection d).stencil.image _ at hq
  obtain ⟨k,hk,rfl⟩:=mem_image.mp hq
  let n:=R.family.side N per
  let J:ℤ:=(b:ℤ)+e a+k a
  have leg:=paid R a inside hk
  have lo:0<J:=by dsimp only [J];omega
  have hi:J<(Cells.half S N per).val:=by dsimp only [J];omega
  have side:=Cells.original S N per
  have jn:J.toNat<n.val:=by change J.toNat<(R.family.S.side N per).val;omega
  have mass: ((wrap n k a+(wrap n e a+o a))-(o a-(b:Per n)):Per n)=(J.toNat:Per n):=by
    have eq':(J.toNat:ℤ)=J:=Int.toNat_of_nonneg lo.le
    have eq:=congrArg (fun t:ℤ=>(t:Per n)) eq'
    change ((k a:ℤ):Per n)+(((e a:ℤ):Per n)+o a)-(o a-(b:Per n))=_
    push_cast [J] at eq
    rw [eq];ring
  change 0<( ((wrap n k a+(wrap n e a+o a))-(o a-(b:Per n)):Per n)).val ∧
    (((wrap n k a+(wrap n e a+o a))-(o a-(b:Per n)):Per n)).val<(Cells.half S N per).val
  rw [mass,ZMod.val_natCast_of_lt jn];omega

/-- A quarter of the requested real reflection spacing, on the true fine
mesh. Independent offsets up to this radius leave every stencilled leg inside. -/
def width (r:ℝ)(N:ℕ):ℕ:=⌊r*(R.family.S.denominator N).val/4⌋₊

theorem paid_width (h:ℕ)(a:Axis){r:ℝ}(small:0<r)(short:r≤1):
    ∀ᶠ N:ℕ in atTop, ∀per:ℕ,
      radius R h a+width R r N<2*width R r N ∧
      2*width R r N+width R r N+radius R h a<(Cells.half S N per).val:=by
  have growing:Tendsto (fun N=>((R.family.S.denominator N).val:ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp R.family.S.den_strict.tendsto_atTop
  filter_upwards [growing.eventually_ge_atTop (4*(radius R h a+1)/r)] with N enough
  have go:radius R h a+1≤width R r N:=by
    apply Nat.le_floor
    have due:4*((radius R h a:ℝ)+1)≤(R.family.S.denominator N).val*r:=(div_le_iff₀ small).mp enough
    push_cast
    linarith
  have den:0<((R.family.S.denominator N).val:ℝ):=by exact_mod_cast (R.family.S.denominator N).property
  have floor:=Nat.floor_le (show 0≤r*(R.family.S.denominator N).val/4 by positivity)
  have share:4*width R r N≤(R.family.S.denominator N).val:=by
    have rt:=mul_le_mul_of_nonneg_right short den.le
    dsimp only [width]
    exact_mod_cast (show (4:ℝ)*⌊r*(R.family.S.denominator N).val/4⌋₊≤(R.family.S.denominator N).val by linarith)
  intro per
  have orig:=Cells.original S N per
  have q4:4≤(R.family.S.period per).val:=Nat.le_of_dvd (R.family.S.period per).property (R.family.S.period_four per)
  change (R.family.S.period per).val*(R.family.S.denominator N).val=2*(Cells.half S N per).val at orig
  have half: (R.family.S.denominator N).val≤(Cells.half S N per).val:=by
    have q2:2≤(R.family.S.period per).val:=(by decide:2≤4).trans q4
    have:= Nat.mul_le_mul_right (R.family.S.denominator N).val q2
    omega
  omega

theorem spacing {r:ℝ}(small:0≤r)(N:ℕ):
    0≤r-4*R.family.S.a N*width R r N ∧ r-4*R.family.S.a N*width R r N<4*R.family.S.a N:=by
  have den:0<(R.family.S.denominator N).val:= (R.family.S.denominator N).property
  have pay:=Nat.floor_le (show 0≤r*(R.family.S.denominator N).val/4 by positivity)
  have back:=Nat.lt_floor_add_one (r*(R.family.S.denominator N).val/4)
  dsimp only [width,Schedule.a]
  constructor
  · field_simp;linarith
  · field_simp;linarith

theorem reflection (r:ℝ)(N per:ℕ)(a:Axis)(o:Site (R.family.side N per)):
    (sheet R N per a o (2*width R r N)).reflect o a=o a-4*(width R r N:Per (R.family.side N per)):=by
  change (sheet R N per a o (2*width R r N)).reflect o (sheet R N per a o (2*width R r N)).pos=_
  rw [Cut.reflect_here]
  dsimp [sheet,Kind.shift];push_cast;ring

end YM.Integration.WilsonPositionOriginalDiagnosticHalfSpace
