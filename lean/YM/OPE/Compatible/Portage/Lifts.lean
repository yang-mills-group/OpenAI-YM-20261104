import YM.OPE.Compatible.Portage.Seen
/-!
# Shared root chart through all depths

Exact centers when certified. Parentage bought in tower used downward.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells Ribbon
open scoped Topology Classical
variable {G:Gauge}(C:Family G){n p i j J:ℕ}
variable (p n J:ℕ)(o:Site (C.side n p))
def axis (i:ℕ)(x:Site (C.side J p)) := bites C J n p o i (x,true)
lemma parents_up {k:ℕ}(h:J≤ i)(hi:i ≤ k)(hk:k≤ n): (C.S.toDepth hi p).parent ∘ axis C p n J o k=axis C p n J o i:= funext fun x=> congr_fun (bitesParent C J n p i o h hi hk) (x,true)
lemma at_zero_axis (h:J ≤ n): axis C p n J o n 0=o:= (biteT C J n p n o h).trans (Ribbons.same C n p o)
lemma peg_width (h:J≤ n)(x:Site (C.side J p)) : width C n p (axis C p n J o n x) (Mix.camp C p J n x)=width C n p o 0:=by
    let v:= Mix.camp C p J n x; rw [show Mix.camp C p J n x=affine (hands C p J x).1 v 0 from (by simp [affine,v]),show axis C p n J o n x= _ from (bit C J n p n o h x true)]; rw [biteT C J n p n o h,Ribbons.same]; exact width_move ..
lemma gap_width (a:Site (C.side n p))(h:J≤ n)(x:Site (C.side J p)): width C n p (axis C p n J o n x) (axis C p n J a n x)=width C n p o a:=by
    dsimp only [axis]; rw [bit C J n p n o h x true,bit C J n p n a h x true, biteT C J n p n o h,biteT C J n p n a h, Ribbons.same,Ribbons.same]; exact width_move ..
lemma spanCopies (a:Site (C.side n p))(h:J≤ n)(x y:Site (C.side J p))(he:x≠y): C.S.a J ≤ width C n p (axis C p n J o n x) (axis C p n J a n y)+width C n p o 0+width C n p a 0:=by
   let q:= Mix.camp C p J n; let A:= axis C p n J o n x; let B:=axis C p n J a n y
   have hx:C.S.a J ≤ width C n p (q x) (q y):=by unfold q; rw [elev C J p n h, elev C J p n h,embed_width]; exact le_mul_of_one_le_right (C.S.a_pos _).le (by exact_mod_cast separation_pos x y he)
   have he : width C n p (q x) A= width C n p o 0:= (width_comm ..).trans (peg_width C p n J o h x)
   have hv:width C n p B (q y)= width C n p a 0:= peg_width C p n J a h y; change _ ≤ width C n p A B+_+_; linarith only [hx,hv,he,width_triangle C p (q x) A (q y),width_triangle C p A B (q y)]
lemma unrolling (h:i ≤ n) (x:Site (C.side i p)) (u:ℕ):
    axis C p n J ((C.S.toDepth h p).embed x) u = axis C p i J x u :=by
   -- only if u≥J? loops all
   funext v; unfold axis bites; simp only [ite_true]; congr 1
   rcases le_total i u with hi|hx
   · rw [vect C i p u x hi]; rcases le_total n u with hn|hm; rw [vect C n p u _ hn,← embed_comp _ _ (C.S.toDepth hi p)]
     rw [vote C n p u _ hm,embed_comp (C.S.toDepth hi p) (C.S.toDepth hm p),Ratio.embed_parent]
   rw [vote C i p u x hx, vote C n p u _ (hx.trans h),parent_nested (C.S.toDepth hx p) (C.S.toDepth h p) _ (C.S.toDepth_odd ..) (C.S.toDepth_odd ..),Ratio.embed_parent]
lemma reel (he:J≤ i)(h:i ≤ n) (x:Site (C.side i p)): Migrating C.path i p n (axis C p n J ((C.S.toDepth h p).embed x)):=by
   rw [show axis C p n J ((C.S.toDepth h p).embed x)=axis C p i J x from funext (unrolling C p n J h x)]
   exact ⟨fun u hq hp=>funext fun v=> congr_fun ((retina C J i p n x he).mare _ hq hp) (v,true)⟩
lemma axis_zero : axis C p n J 0=Mix.camp C p J:=by
   funext i v; unfold axis bites; simp only [ite_true,affine]; unfold loops; split
   next h=> rw [show (C.S.toDepth h p).embed 0=0 from (C.S.toDepth h p).root.map_zero,Signed.act_zero,zero_add]
   next h => let a:=C.S.toDepth (p:=p) (show i ≤ n by omega); have hz:a.parent 0=0:=by have he:=a.embed_parent 0; rwa [show a.embed 0=0 from a.root.map_zero] at he
             change _+(Mix.camp C p J i v)=(Mix.camp C p J i v); rw [hz,Signed.act_zero,zero_add]
end YM.OPE.Arboreal.Pixel
