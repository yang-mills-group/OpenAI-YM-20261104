import YM.Extraction.Banks
import YM.Integration.WilsonPositionOriginalDressedQCylinder

/-! The reflected receiving cell and its propagated Wilson stencil use the
fixed original origin plane at each cutoff.  Each admissible lift may be
chosen from the actual reporter sampling support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQFixedPlane
open Filter Set Function MeasureTheory Lattice Wilson RG Source Labels Cells Extraction.Banks
open PhysicalNext.Repeat.Legato Push.GridApprox WilsonPositionOriginalDressedQCylinder
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "S"=>R.family.S
local notation "A"=>R.family.path.levels
local notation "Λ"=>RG16.Lambda A

private theorem sector (N per:ℕ)(a:Axis)(u:Cover)(q:ℕ)
    (lower:(q:ℤ)<u a)(upper:u a+q<(Cells.half S N per).val):
    window (wrap (R.family.side N per) u) q ⊆ (plane R.family N per a).sector:=by
  rintro _ ⟨v,hv,rfl⟩
  change v∈Finset.Icc _ _ at hv
  have low:-(q:ℤ)≤v a:=(Finset.mem_Icc.mp hv).1 a
  have high:v a≤(q:ℤ):=(Finset.mem_Icc.mp hv).2 a
  let n:=R.family.side N per
  let J:=v a+u a
  have first:0<J:=by dsimp only [J];omega
  have last:J<(Cells.half S N per).val:=by dsimp only [J];omega
  have side:=Cells.original S N per
  have jn:J.toNat<n.val:=by change J.toNat<(R.family.S.side N per).val;omega
  have clock:((wrap n v a+wrap n u a)-0:Per n)=(J.toNat:Per n):=by
    change ((v a:ℤ):Per n)+((u a:ℤ):Per n)-0=_
    have eq:=congrArg (fun t:ℤ=>(t:Per n)) (Int.toNat_of_nonneg first.le)
    calc
      _ = ((J:ℤ):Per n):=by simp [J]
      _ = _:=by simpa only [Int.cast_natCast] using eq.symm
  change 0<(((wrap n v a+wrap n u a)-0:Per n)).val ∧
    (((wrap n v a+wrap n u a)-0:Per n)).val<(Cells.half S N per).val
  rw [clock,ZMod.val_natCast_of_lt jn];omega

private theorem half_span (N per:ℕ):2≤R.family.S.a N*(Cells.half S N per).val:=by
  have side:=Cells.original S N per
  have realSide:((R.family.S.side N per).val:ℝ)=2*((Cells.half S N per).val:ℝ):=by exact_mod_cast side
  have four:=R.family.S.period_four per
  have positive:0<(R.family.S.period per).val:=(R.family.S.period per).property
  have g:(4:ℝ)≤(R.family.S.period per).val:=by exact_mod_cast (show 4≤(R.family.S.period per).val by omega)
  have span:=R.family.S.span_side N per
  rw [realSide] at span
  linarith

/-- Positive-time original reporting sites, including their full coarse
Wilson posterior support, lie on the same physical plane as the fixed
original dressed-column Gram before the two ordered regulator limits. -/
theorem original (Y:OPE.Therm.Poetry A)(simple:G.Simple)(h:ℕ):
    ∀ᶠ m:ℕ in atTop,∀ r:ℝ,0<r → r≤1 → 2*R.family.S.a m*(Λ m)^2≤r →
      ∀w:ℕ,8*R.family.S.a m*w≤r → ∀N per,∀live:m≤N,∀a:Axis,∀u:Cover,
      r/2≤R.family.S.a m*(u a:ℝ) → R.family.S.a m*(u a:ℝ)≤1 →
      window (anchor S per live (wrap (R.family.S.side m per) u)) (grows A m (w+stencil R h) live)
        ⊆ (plane R.family N per a).sector:=by
  filter_upwards [current R Y simple h] with m paid
  intro r hr small enough w offset N per live a u lower upper
  let d:=R.family.S.toDepth live per
  let q:=grows A m (w+stencil R h) live
  have native:=scales_budget A m (w+stencil R h) live
  have tail_nonneg:0≤tail A N:=(tail_pos ..).le
  have num:4*R.family.S.a N*(q:ℝ)≤r:=by
    push_cast at native
    dsimp only [q]
    linarith only [native,paid,offset,enough,tail_nonneg]
  have carried:R.family.S.a N*((d.count.val • u) a:ℝ)=R.family.S.a m*(u a:ℝ):=by
    rw [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←mul_assoc,R.family.S.embeds_scale d]
  have pos:=R.family.S.a_pos N
  have span:=half_span R N per
  change window (d.embed (wrap (R.family.S.side m per) u)) q ⊆ _
  rw [d.embed_wrap]
  apply sector R N per a
  · have bound:(q:ℝ)<((d.count.val • u) a:ℝ):=by
      apply lt_of_mul_lt_mul_left (a:=R.family.S.a N) _ pos.le
      rw [carried]
      linarith only [num,lower,hr]
    exact_mod_cast bound
  · have bound:(((d.count.val • u) a:ℝ)+(q:ℝ))<((Cells.half S N per).val:ℝ):=by
      apply lt_of_mul_lt_mul_left (a:=R.family.S.a N) _ pos.le
      rw [mul_add,carried]
      linarith only [num,upper,small,span]
    exact_mod_cast bound

end YM.Integration.WilsonPositionOriginalDressedQFixedPlane
