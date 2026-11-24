import YM.OPE.Compatible.Dale.Ford
/-!
# Links and block match
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Weir
open Function Filter Lattice Laurent Tree Woody Finset
open scoped Topology BigOperators ComplexConjugate
variable {n c f:Side}
abbrev edgeV (n:Side):= Edge (Site n)
def ferry (k:Kv)(x:edgeV n):= ((posDir x.2).rotate (axisK k)).used (decks k x.1)
@[simp] lemma ferry_axis (k:Kv)(x:edgeV n): (ferry k x).2=x.2:=by unfold ferry Step.used; split <;> rfl
@[simp] lemma ferry_0 (x:edgeV n): ferry 0 x=x:=by simp only [ferry,axisK_id,flats,Step.rotate_one]; rfl
lemma ferry_read (k:Kv)(x:Site n)(d:Step): ferry k (d.used x)=(d.rotate (axisK k)).used (decks k x):=by
     rcases d with ⟨i,b⟩; cases b
     · rfl
     change (((posDir i).rotate _).used (decks k (x-step i)))=((negDir i).rotate _).used _
     have he:= decks_walk k (x-step i) (posDir i); simp only [Step.vec_pos,sub_add_cancel] at he
     rw [he,show negDir i=(posDir i).rev from rfl,Step.rev_rotate]; let a:= (posDir i).rotate (axisK k); have h(d:Step)(u:Site n): d.rev.used (u+d.vec)=d.used u:=by cases d with | mk j b=> cases b <;>simp [Step.rev,Step.vec,Step.used,sub_eq_add_neg]
     exact (h a _).symm
variable (H:Even n.val)
include H
@[simp] lemma ferry_plus (k h:Kv)(x:edgeV n):ferry (k+h) x=ferry k (ferry h x):=by
    rw [ferry,axisK_plus,← Step.rotate_mul, decks_plus H]; exact (ferry_read ..).symm
def swoop (k:Kv): edgeV n ≃ edgeV n:=⟨ferry k,ferry k,fun x=>by rw [← ferry_plus H,twinned,ferry_0],fun x=>by rw [← ferry_plus H,twinned,ferry_0]⟩
lemma vary_decks (k:Kv)(h:k≠0)(p:Site n): decks k p ≠ p:=by
    have he:= deck_free _ h p; intro hh; rw [hh,separation_self] at he; have hp:0 < n.val:=n.pos; obtain ⟨j,hj⟩:=H; omega
-- deck bond displacement at least n/2 in invariant coordinate
lemma ferry_free (k:Kv)(h:k≠0)(p:edgeV n): ferry k p≠p:=by
    obtain ⟨i,hi,hq⟩:= axis_free h
    intro e
    have hz : (decks k p.1) i=p.1 i:=by
       unfold ferry Step.used at e; split at e
       next he=>
         have hb:i≠ p.2:=by intro hb; simp [Step.rotate,posDir,← hb,hi] at he
         have ha:=congr_arg (fun q:edgeV n=>q.1 i) e; dsimp only [Pi.sub_apply] at ha; rw [show ((posDir p.2).rotate (axisK k)).dir=p.2 from rfl, step_apply, if_neg hb,sub_zero] at ha; exact ha
       next he=> exact congr_arg (fun q:edgeV n=>q.1 i) e
    change (axisK k).act p.1 ((axisK k).perm i)+offset k n i=p.1 i at hz; rw [Signed.act_at,hi,if_neg (by decide),offset,hq,if_pos rfl] at hz
    have hv: ((n.val/2:ℕ):Per n)=0:=add_eq_left.mp hz
    rw [ZMod.natCast_eq_zero_iff] at hv
    obtain ⟨j,hj⟩:=H; have hp:0<n.val:=n.pos; have he:= Nat.le_of_dvd (by omega) hv; omega
omit H
variable (g:Ratio c f) (hp: Even c.val)
include hp g
lemma even_both: Even f.val:=by rw [g.exact_size]; exact hp.mul_right _ -- g omitted
lemma offset_step (k:Kv): g.embed (offset k c)= offset k f:=by
    let v:Cover:=fun i=> if moveK k i then ((c.val/2:ℕ):ℤ) else 0
    have hu: offset k c=wrap c v:=funext fun i=>by
       unfold offset; split_ifs with hd
       · change _= Int.cast (v i); unfold v; rw [if_pos hd,Int.cast_natCast]
       change _=Int.cast (v i); unfold v; rw [if_neg hd,Int.cast_zero]
    rw [hu,g.embed_wrap]; funext i; change Int.cast ((g.count.val • v : Cover) i)=ite _ _ _; rw [Pi.smul_apply, nsmul_eq_mul]; unfold v; split_ifs
    next h=>
       rw [← Nat.cast_mul,Int.cast_natCast]; congr 1
       obtain ⟨j,hj⟩:=hp; rw [g.exact_size,hj,show (j+j)/2=j by omega,Nat.add_mul]; rw [Nat.mul_comm]; omega
    next h=>rw [mul_zero,Int.cast_zero]
lemma step_charm (k:Kv)(x:Site c): g.embed (decks k x)=decks k (g.embed x):=by
    unfold decks affine; rw [← Ratio.root_embed, map_add]; simp [offset_step g hp]
lemma step_leaf (hq:Odd g.count.val)(k:Kv)(x:Site c)(y:Site g.count): decks k (g.assemble (x,y))=g.assemble (decks k x,(axisK k).act y) := by
    simp only [Ratio.assemble]; rw [step_charm g hp]; unfold decks affine; rw [Signed.act_add,wrap_signed,Ratio.lift_signed_of_odd hq]; abel
lemma step_parent (hq:Odd g.count.val)(k:Kv)(x:Site f): g.parent (decks k x)=decks k (g.parent x) ∧ g.residue (decks k x)=(axisK k).act (g.residue x):=by
   obtain ⟨⟨x,y⟩,rfl⟩:=g.assemble_bijective.surjective x; simp [step_leaf g hp hq]
lemma winch (hq:Odd g.count.val)(k:Kv)(x:Site f)(hy:leaf g x):leaf g (decks k x) ∧ (forest g hq).up (decks k x)=((forest g hq).up x).rotate (axisK k):=by
     rw [leaves g _] at *; simp only [forest,(step_parent g hp hq k x).2,rises (axisK k) (axis_pin _) hq hy, and_true]; intro hh; apply hy; exact (axisK k).act_injective (hh.trans (Signed.act_zero ..).symm)
lemma staff_at (hq:Odd g.count.val)(k:Kv)(p:edgeV f)(h:p∈(forest g hq).trunks): ferry k p∈(forest g hq).trunks:=by
     rw [Forest.trunk_mem_iff] at *; obtain ⟨i,hi,hx⟩:=h; rw [←hx,ferry_read]; obtain ⟨hz,hH⟩:= winch g hp hq k i hi; exact ⟨_,hz,by rw [hH]⟩
end YM.OPE.Weir
