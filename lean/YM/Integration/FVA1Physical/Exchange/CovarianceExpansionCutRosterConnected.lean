import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCutRosterSum
import YM.Comparison.RG02.Cumulants.Split

/-! A signed hard cofactor vanishes on an actual physical field if all its
live actor tables occupy just one side of a spatial cut. The scalar denominator
belongs to that original field. This gives a support criterion; it does not
bound the magnitude of a cofactor whose physical actor network crosses the cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Primitives.GCC.Anchor
  Comparison.RG02.Cumulants
open scoped Classical BigOperators
open private owner_of_product scalar_row from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionActualRoster
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

omit [Fintype V] in
private theorem region_absent (B:Activities G n)(E:Support n)(K:ℕ→Poly C)(c:ℕ→Prop)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))(v:V)
    (miss:∀i,c i → ∀m:C.Mode,v∈m.val → (K i).part m=0)
    (s:C.Mode)(used:v∈s.val):
    (∑'L:Pool c,component B E K L.val).part s=0:=by
  rw [Poly.share (regional_series B E K w wp stock c)]
  trans ∑'_:Pool c,(0:ℂ)
  swap
  · exact tsum_zero
  apply tsum_congr
  intro L
  unfold component
  split
  · by_contra nz
    obtain ⟨i,hi,r,_,vr,kr⟩:=owner_of_product K L.val s v used nz
    exact kr (miss i (L.property i hi) r vr)
  rfl

private theorem connected_absent (H:Poly C)(unit:H.part C.quiet=1)(v:V)
    (miss:∀s:C.Mode,v∈s.val → H.part s=0)(s:C.Mode)(used:v∈s.val):
    (connected H).part s=0:=by
  have same:without {v} H=H:=by
    ext r
    rw [begin_outer_part]
    by_cases hr:v∈r.val
    · rw [if_neg (fun h=>disjoint_singleton_right.mp h hr),miss r hr]
    rw [if_pos (disjoint_singleton_right.mpr hr)]
  have e:(connected H).part s=(without {v} (connected H)).part s:=by
    rw [←conn_outside _ H unit,same]
  rw [e,begin_outer_part,if_neg (fun h=>disjoint_singleton_right.mp h used)]

/-- Two marked sites on opposite sides cannot contribute to the exact log
density on a physical input without an active actor crossing that cut. This
includes the original unmarked gas on the complete compulsory failure set. -/
theorem original_mixed_vanishes (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (D:Support n)(nocross:∀i,K i≠0 → ¬lies B D i → Disjoint (B.forced i).support D)
    (o:V→Site n)(carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))(live:B.gas p U≠0)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))
    (s:C.Mode)(a b:V)(usedA:a∈s.val)(usedB:b∈s.val)(left:o a∈D)(right:o b∉D):
    (connected (((B.gas p U:ℂ)⁻¹) • ∑'S,RoseRoster.roster B p U K S)).part s=0:=by
  let l:=∑'L:Pool (lies B D),component B (flags p.threshold U∩D) K L.val
  let r:=∑'R:Pool (fun i=>¬lies B D i),component B (flags p.threshold U\D) K R.val
  let ν:ℂ:=B.gas p U
  have fact:(∑'S,RoseRoster.roster B p U K S)=l*r:=
    original_full_cut B p U K D nocross w wp stock
  have quiet:l.part C.quiet * r.part C.quiet=ν:=by
    rw [←Poly.quiet_mul,←fact,Poly.share (physical_series B p U K w wp stock)]
    simp_rw [scalar_row B p U K K₀]
    exact (Complex.ofReal_tsum _).symm
  have both:l.part C.quiet * r.part C.quiet≠0:=quiet ▸ Complex.ofReal_ne_zero.mpr live
  let x:Poly C:=(l.part C.quiet)⁻¹ • l
  let y:Poly C:=(r.part C.quiet)⁻¹ • r
  have u:x.part C.quiet=1:=by
    change ((l.part C.quiet)⁻¹ • l).part C.quiet=1
    rw [Poly.part_smul,inv_mul_cancel₀ (left_ne_zero_of_mul both)]
  have z:y.part C.quiet=1:=by
    change ((r.part C.quiet)⁻¹ • r).part C.quiet=1
    rw [Poly.part_smul,inv_mul_cancel₀ (right_ne_zero_of_mul both)]
  have factor:ν⁻¹ • (l*r)=x*y:=by
    dsimp only [x,y]
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,←mul_inv,quiet]
  have west (m:C.Mode)(marked:b∈m.val):x.part m=0:=by
    change ((l.part C.quiet)⁻¹ • l).part m=0
    rw [Poly.part_smul]
    apply mul_eq_zero_of_right
    apply region_absent B _ K _ w wp stock b _ m marked
    intro i within f used
    by_contra nz
    exact right (within (carry i f nz b used))
  have east (m:C.Mode)(marked:a∈m.val):y.part m=0:=by
    change ((r.part C.quiet)⁻¹ • r).part m=0
    rw [Poly.part_smul]
    apply mul_eq_zero_of_right
    apply region_absent B _ K _ w wp stock a _ m marked
    intro i outside f used
    by_contra nz
    have active:K i≠0:=by rintro h;exact nz (by rw [h];rfl)
    exact disjoint_left.mp (nocross i active outside) (carry i f nz a used) left
  change (connected (ν⁻¹ • ∑'S,RoseRoster.roster B p U K S)).part s=0
  rw [fact,factor,connected_mul u z,Poly.part_plus,
    connected_absent x u b west s usedB,connected_absent y z a east s usedA,add_zero]

end YM.Integration.FVA1Physical.Exchange.RoseCut
