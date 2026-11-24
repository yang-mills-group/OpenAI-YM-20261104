import YM.RegulatorIR.Geometry.Edges
import YM.Tree.Cut

/-! Bind orbit orientations to a usable rooted symmetric Tree. Choose up = erase
least still nonzero axis (thus straight path to root, fixed ordering injection to
coordinate witnesses). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Function Lattice PertExtension Orb Gauge Tree Tree.Forest
open scoped ENNReal NNReal BigOperators Classical Topology
variable {c f:Side} (g:Ratio c f)(hp:Odd g.count.val)
namespace Fibers
include hp
lemma neg_lift (x:Site g.count): Lattice.lift (-x)= -Lattice.lift x:=by
 apply lift_eq_iff.mpr
 refine ⟨?_,?_⟩
 · rw [map_neg,wrap_lift]
 intro i; have h:= Ratio.unambiguous hp x i; have hh:= lift_centers x i; simp only [Pi.neg_apply]; omega
lemma other_parent (x: Site f) : g.parent (-x)=-g.parent x:=by
 apply g.embed_injective
 have h:= Ratio.unpack_at g (-x)
 have hv : wrap f (Lattice.lift (g.residue (-x))) = -(wrap f (Lattice.lift (g.residue x))):=by simp only [map_neg,neg_lift g hp]
 have hsub:= Ratio.unpack_at g x
 apply add_right_cancel (b:= wrap f (Lattice.lift (g.residue (-x))))
 rw [h,hv, show g.embed (-g.parent x)= -g.embed (g.parent x) from g.root.map_neg _,← neg_add,hsub]
lemma leaf_neg (x: Site f):leaf g (-x) ↔ leaf g x:=by
 change -x≠g.embed (g.parent (-x)) ↔ x≠_
 rw [other_parent g hp,show g.embed (-g.parent x)= -g.embed (g.parent x) from g.root.map_neg _]; simp
lemma fixed_root (x: Site f)(h:-x=x): g.residue x=0 := by
 let a:=g.residue x
 have hs : -a=a:= (g.residue.map_neg _).symm.trans (congr_arg g.residue h)
 have ht (i:Axis) := congr_fun (neg_lift g hp a) i
 have hh:Lattice.lift a=0:=by
    ext1 i; specialize ht i; rw [hs,Pi.neg_apply] at ht; change _=0;omega
 exact (wrap_lift a).symm.trans (by rw [hh,map_zero])
omit hp in
lemma shifted_leaf (x: Site f)(y:Site c): leaf g (x+g.embed y)↔ leaf g x:=by
 change _≠g.embed (g.parent _) ↔ _≠_
 simp only [ne_eq, Ratio.root_id,map_add,Ratio.residue_embed, add_zero]
end Fibers
open Fibers
namespace Bark
variable (x:Site f)
def slot := Lattice.lift (g.residue x)
omit hp in
lemma occupied (h:leaf g x): ∃ i,slot g x i ≠0:=by
 by_contra! hh
 have h': slot g x=0:=funext hh
 exact h ((g.root_id x).mpr (by rw [← wrap_lift (g.residue x)];change wrap _ (slot g x)=_;rw [h',map_zero]))
def active := Finset.univ.filter fun i=>slot g x i≠0
lemma reserve (h:leaf g x): (active g x).Nonempty:= by
 obtain ⟨i,hi⟩:= occupied g x h; exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
def slim (h:leaf g x) : Axis:= (active g x).min' (reserve g x h)
lemma wise (h:leaf g x): slot g x (slim g x h)≠0 := (Finset.mem_filter.mp (Finset.min'_mem (active g x) (reserve g x h))).2
include hp in
lemma slimmed (h:leaf g (-x))(hd:leaf g x): slim g (-x) h=slim g x hd:=by
 unfold slim; congr 1
 ext1 i; unfold active slot;rw [map_neg,neg_lift g hp];simp

def toward (h:leaf g x): Step := if slot g x (slim g x h)<0 then posDir (slim g x h) else negDir (slim g x h)
include hp in
lemma weighs (h:leaf g x) : Laurent.size (slot g (x+(toward g x h).vec)) < Laurent.size (slot g x) ∧ g.parent (x+(toward g x h).vec)=g.parent x:=by
 let i:= slim g x h; let d:= toward g x h; let u:= slot g x; let l:=g.count.val/2
 have hZ : u i ≠ 0 := wise g x h
 have hT : d= if u i <0 then posDir i else negDir i := rfl
 have h' j (hd:j≠i):(u+d.vec:Cover) j=u j:=by rw [hT];split_ifs <;> simp [hd]
 have ht : u+d.vec ∈ box l:=by
    rw [box_iff_layers]; intro j; by_cases he:j=i
    · subst j; have h:(u i)∈ layers l:= (box_iff_layers ..).mp (g.half_box hp (g.residue x)) i
      rw [hT]; split_ifs <;> simp [layers] at * <;> omega
    rw [h' j he]; exact (box_iff_layers ..).mp (g.half_box hp (g.residue x)) j
 obtain ⟨hr,H⟩:= g.internal hp (x:=x) (i:=d) ht
 refine ⟨?_,H⟩; change Laurent.size (Lattice.lift _)< _
 rw [hr]; change Laurent.size (u+d.vec) < Laurent.size u
 have hv : ((u+d.vec : Cover) i).natAbs < (u i).natAbs:=by rw [hT];split_ifs <;> simp <;> omega
 exact Finset.sum_lt_sum (fun j _=> by by_cases hp:j=i; subst j; exact hv.le; rw [h' j hp]) ⟨i, Finset.mem_univ _,hv⟩
include hp in
lemma cost : Laurent.size (slot g x) ≤4*g.count.val:=by
 apply le_trans _ (show (∑ _:Axis,g.count.val)=4*g.count.val from by simp).le -- adjust
 apply Finset.sum_le_sum
 intro i _; have h:= (box_iff_layers ..).mp (g.half_box hp (g.residue x)) i
 unfold layers at h; rw [Finset.mem_Icc] at h; unfold slot; omega

def proper (hp:Odd g.count.val): Forest g where
 up x:= if h:leaf g x then toward g x h else posDir 0
 height x:= Laurent.size (slot g x)
 bound x:= cost g hp x
 rise x h:= by rw [dif_pos h]; exact (weighs g hp x h).1
 stays x h:= by rw [dif_pos h]; exact (weighs g hp x h).2
lemma tilt (h:leaf g x): (proper g hp).up (-x)= ((proper g hp).up x).rev:=by
 let hf:= (leaf_neg g hp x).mpr h; let i:= slim g x h
 have h': slot g (-x)= -slot g x:= by unfold slot;rw [map_neg,neg_lift g hp];
 have he:= wise g x h
 dsimp only [proper]; rw [dif_pos hf, dif_pos h]; simp only [toward,slimmed g hp x hf h,h',Pi.neg_apply]; split_ifs <;> first | rfl | omega
lemma repeat_patch (y:Site c): (proper g hp).up (x+g.embed y)= (proper g hp).up x:=by
 have hz : slot g (x+g.embed y)=slot g x:=by simp [slot]
 dsimp only [proper]; split_ifs with he hp' hx
 · have h': slim g (x+g.embed y) he=slim g x hp':=by unfold slim; congr 1; ext i;simp [active,hz]
   unfold toward; rw [hz,h']
 · exact (hp' ((shifted_leaf g ..).1 he)).elim
 · exact (he ((shifted_leaf g ..).2 hx)).elim
 rfl
end Bark
end YM.RegulatorIR.Geometry
