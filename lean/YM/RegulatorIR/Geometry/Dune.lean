import YM.RegulatorIR.Geometry.Forest
import YM.PertExtension.OrbHaar

/-! Root-equivariant gauges on quotient links. On a block step use only
translated and inversion-compatible forests, not arbitrary random branches.
Global group at each fixed root OK; no fixed site k-branch solved with
independent variables. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Function Set Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest Fibers
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f:Side}{g:Ratio c f} {G:Gauge}
abbrev spins (G:Gauge) (f:Side):= OEdge f → G.El -- change abbrev
abbrev orbLift (U:spins G f) := liftLinks U
def compatible (k: Site f→ G.El): Prop:= ∀ x,k (-x)=k x
lemma identity_comp : compatible (G:=G) (f:=f) 1:=fun _=> rfl
lemma mul_comp {u v:Site f→G.El}(h:compatible u)(hh:compatible v):compatible (u*v):=fun i=>congr_arg₂ (·*·) (h i) (hh i)
lemma inv_comp {u:Site f→G.El}(h:compatible u): compatible u⁻¹:= fun i=> congr_arg (·⁻¹) (h i)
lemma lift_site {k:Site c→ G.El}(he:Odd g.count.val)(h:compatible k): compatible (fun x=>k (g.parent x)) :=by intro i; dsimp only; rw [Fibers.other_parent g he]; exact h _
lemma restrict_site {k:Site f→ G.El}(h:compatible k): compatible (fun i=>k (g.embed i)) :=by intro i; dsimp only; rw [show g.embed (-i) = -(g.embed i) from g.root.map_neg _]; exact h _
lemma is_sheet (U : Config G f)(h:∀ i,U (reflect i)=(U i)⁻¹): ∃ V:spins G f, U=orbLift V:= by
 refine ⟨fun i=>U i.val,?_⟩; ext1 i; by_cases ht:eR i=i
 · let j:OEdge f:=⟨i,ht⟩; exact (lift_at (fun i : OEdge f=> U i.val) j).symm
 have hz: eR i=reflect i:= (eR_spec i).resolve_left ht
 change U i= if eR i=i then U (eR i) else (U (eR i))⁻¹
 rw [if_neg ht,hz,h, inv_inv]

lemma stayed (A:Forest g)(p:Site f)(h: Odd g.count.val)(he:∀ i,leaf g i→ A.up (-i)=(A.up i).rev): A.hike (-p)=(A.hike p).map Step.rev:=by
 induction p using Forest.hike.induct A with
 | case1 x hx ih=>
   have hr:= he x hx
   nth_rw 1 [Forest.hike, dif_pos ((leaf_neg g h x).mpr hx), hr]; rw [show -x+_= -(x+(A.up x).vec) by rw [hr,Step.vec_rev]; abel,ih]
   rw [show A.hike x=A.up x::A.hike (x+(A.up x).vec) from by rw [Forest.hike,dif_pos hx]]; rfl
 | case2 x hx=> rw [Forest.hike,dif_neg fun h'=>hx ((leaf_neg g h x).mp h'),Forest.hike, dif_neg hx]; rfl

namespace Field
variable (F:Forest g)
structure Square : Prop where
  odd : Odd g.count.val
  preserves : ∀ i, leaf g i→ F.up (-i)=(F.up i).rev
  translated : ∀ (i:Site f) (j:Site c), F.up (i+g.embed j)=F.up i
lemma Square.proper (g:Ratio c f)(h:Odd g.count.val): Square (Bark.proper g h):= ⟨h,Bark.tilt g h, Bark.repeat_patch g h⟩
-- descend

def branch (e:OEdge f): Prop:= e.val∈F.trunks
abbrev Knot := {i : OEdge f // branch F i}
abbrev Wind := {i : OEdge f // ¬branch F i}
variable {F}
lemma roots (h:Square F)(x:Site f)(hx:-x=x): ¬ leaf g x:=fun hh=> hh ((g.root_id x).mpr (fixed_root g h.odd x hx))
lemma reflect_trunk (h:Square F){e:Edge (Site f)}(H:e∈ F.trunks): reflect e∈F.trunks:=by
 obtain ⟨i,hi,rfl⟩:= (F.trunk_mem_iff _).mp H
 apply (F.trunk_mem_iff _).mpr; exact ⟨-i,(leaf_neg g h.odd _).mpr hi,by rw [h.preserves i hi]; exact Orb.used_flip ..⟩
lemma bone (h:Square F)(e:Edge (Site f)): branch F (index e)↔ e∈ F.trunks := by
 change eR e∈ _ ↔ _; rcases eR_spec e with hh|hh
 · rw [hh]
 rw [hh]; exact ⟨fun p=> reflect_reflect e ▸ reflect_trunk h p,reflect_trunk h⟩
lemma lifts_fold (h:Square F)(U:spins G f)(hv:Even f.val) : compatible (F.foldAt (orbLift U)) := by
 have he (w:Walk) (x: Site f): travel (orbLift U) (-x) (w.map Step.rev)=travel (orbLift U) x w := by
   induction w generalizing x with
   | nil=> rfl
   | cons d w ih=>rw [List.map_cons,travel,travel,Step.vec_rev,← neg_add,ih];apply congr_arg (·* (travel ..))
                  -- steps
                  unfold Step.read; rw [Orb.used_flip, show orbLift U (reflect _)=(orbLift U _)⁻¹ from lift_flip hv U _]; cases h:d.neg <;> simp [Step.rev,h]
 intro x;rw [foldAt, foldAt,stayed F x h.odd h.preserves,he]
end Field
end YM.RegulatorIR.Geometry
