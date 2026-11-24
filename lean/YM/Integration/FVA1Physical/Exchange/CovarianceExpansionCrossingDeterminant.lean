import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDebt

/-! Exact original signed connected pair after deleting only actors crossing
a nominated territory. The cut scalar is allowed to vanish. The four crossing
rows are signed sums of complete original admissible rosters. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Comparison.RG02.Cumulants
  Primitives.GCC.Anchor QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

omit [Fintype V] in
private theorem separated_determinant (cut:Poly C)(O:Finset V)(l r:Poly C)
    (rows:∀s:C.Mode,cut.part s=l.part (inside s O)*r.part (diff s O))
    (a b:V)(left:a∈O)(right:b∉O)(s:C.Mode)(pair:s.val={a,b}):
    cut.part C.quiet*cut.part s=cut.part (C.fire a)*cut.part (C.fire b):=by
  have q0:inside C.quiet O=C.quiet:=Subtype.ext (empty_inter O)
  have q1:diff C.quiet O=C.quiet:=Subtype.ext (empty_sdiff O)
  have aa:inside (C.fire a) O=C.fire a:=Subtype.ext (inter_eq_left.mpr (singleton_subset_iff.mpr left))
  have az:diff (C.fire a) O=C.quiet:=Subtype.ext (sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr left))
  have bz:inside (C.fire b) O=C.quiet:=Subtype.ext (Finset.disjoint_iff_inter_eq_empty.mp (disjoint_singleton_left.mpr right))
  have bb:diff (C.fire b) O=C.fire b:=Subtype.ext (sdiff_eq_self_of_disjoint (disjoint_singleton_left.mpr right))
  have ab:inside s O=C.fire a:=by
    apply Subtype.ext
    change s.val∩O={a}
    rw [pair]
    ext v
    simp only [mem_inter,mem_insert,mem_singleton]
    grind
  have ba:diff s O=C.fire b:=by
    apply Subtype.ext
    change s.val\O={b}
    rw [pair]
    ext v
    simp only [mem_sdiff,mem_insert,mem_singleton]
    grind
  rw [rows C.quiet,rows s,rows (C.fire a),rows (C.fire b),q0,q1,aa,az,bz,bb,ab,ba]
  ring

/-- No cut denominator on either side; both singleton means use the full
original vacuum. In particular the scalar crossing is a real input to the
signed error, even if every distinguished long actor has only a vacuum row. -/
theorem filed_crossing_determinant {w:V→ℝ}(wp:∀v,0<w v){e c:ℝ}
    (paid:A.K.Paid w P.p.B e c)(en:0≤e)(t:T)(U:Config G n)(live:0<P.eval U)
    (L:Support n)(a b:V)(insideA:o a∈L)(outsideB:o b∉L)(s:C.Mode)(pair:s.val={a,b}):
    let ν:ℂ:=P.activities.gas P.p U
    let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
    let u:=(A.gas t U).part (C.fire a)/ν
    let v:=(A.gas t U).part (C.fire b)/ν
    (ν-E.part C.quiet)*(ν*filedRow A t s U-
      (E.part s-u*E.part (C.fire b)-v*E.part (C.fire a)+u*v*E.part C.quiet))=
      (E.part (C.fire a)-u*E.part C.quiet)*(E.part (C.fire b)-v*E.part C.quiet):=by
  intro ν E u v
  let K:=fun i=>A.K.hard t i U
  let cut:=remainingCash P.activities P.p U K L
  let O:=univ.filter fun i=>o i∈L
  have nz:ν≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
  have stock:=filed_actor_stock A wp paid en t U
  have exactSum:A.gas t U=cut+E:=crossing_cash_exact P.activities P.p U K L w wp stock
  have cutRow (z:C.Mode):cut.part z=(A.gas t U).part z-E.part z:=by
    rw [exactSum,Poly.part_plus,add_sub_cancel_right]
  obtain ⟨l,r,pin⟩:=retained_reads P.activities P.p U K L o (fun i z=>(A.K.locality t i).carry U z) w wp stock
  have left:a∈O:=mem_filter.mpr ⟨mem_univ _,insideA⟩
  have right:b∉O:=fun h=>outsideB (mem_filter.mp h).2
  have eq:=separated_determinant cut O l r pin a b left right s pair
  have base:(A.gas t U).part C.quiet=ν:=Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid en wp t U)
  have unit:((ν⁻¹) • A.gas t U).part C.quiet=1:=by rw [Poly.part_smul,base,inv_mul_cancel₀ nz]
  have dist:a≠b:=by rintro rfl;exact outsideB insideA
  have pairRow:=twins a b s (ν⁻¹ • A.gas t U) unit dist pair
  change (ν-E.part C.quiet)*(ν*(connected (ν⁻¹ • A.gas t U)).part s-_)=_
  rw [pairRow]
  simp only [Poly.part_smul,cutRow,base] at eq ⊢
  dsimp only [u,v]
  field_simp [nz]
  linear_combination ν^2*eq

end YM.Integration.FVA1Physical.Exchange.RoseCut
