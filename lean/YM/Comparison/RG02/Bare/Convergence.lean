import YM.Comparison.RG02.Bare.Eligible
import YM.Tree.Cut
/-!
# Combining on the genuine gauge slice

 Detection of zero-energy orbits on the Wilson step by the long Wilson paths of predicted anchors.
 Show that being flat AND giving unit on the coarse links kills all remaining holonomy here
 (including if the anchor path goes across the torus seam). This is useful for finite-regulator
 Laplace tests with the actual kernel, without even changing S.tree or using inversion regulators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory Lattice Wilson Tree Pressure RG
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {c f : Side} {G : Gauge} {U : Config G f}
variable (S : StepData c f)
local notation "P"=> S.patch
local notation "E" => S.ratio.embed
local notation "L"=> S.patch.L.val
variable (h : S.patch.Branches S.kernel G) (ht : Flat U)
lemma ground_floor (a : G.El) (he : G.price a=0): a=1 := by
   have hC := G.chord_price a
   rw [he,mul_zero] at hC; have h0 : G.chord a=0:= by nlinarith [hC]
   apply G.mat_injective; unfold Gauge.chord at h0; rw [div_eq_zero_iff] at h0
   rcases h0 with hx|hx; exact sub_eq_zero.mp (norm_eq_zero.mp hx)
   exact ((Real.sqrt_pos_of_pos (show 0<(G.repDim:ℝ) from by exact_mod_cast G.dimPos)).ne' hx).elim
lemma flat_pin (he : energy U=0) : Flat U := fun i=> ground_floor _ ((Finset.sum_eq_zero_iff_of_nonneg (fun p (_:p∈Finset.univ)=> (G.price_range (faceValue U p)).1)).mp he i (Finset.mem_univ _))

private def downwalk (d : Step) : Walk:= if d.neg then Lattice.reverse (S.repath d.dir) else S.repath d.dir
private lemma back (x : Site c) (i : Axis) : E (x-step i) + L • step i = E x:= by rw [← S.leap, sub_add_cancel]
lemma advance_stop (x : Site c) (i : Axis): stop (E x) (S.repath i) = E (x+step i):= (S.stop_repath ..).trans (S.leap ..).symm
lemma stop_one (x : Site c) (d : Step) : stop (E x) (downwalk S d)= E (x+d.vec):= by
   cases d with | mk i b=>
   cases b; exact advance_stop ..
   change stop (E x) (Lattice.reverse _)=E (x+-step i); rw [← sub_eq_add_neg]; nth_rw 1 [← (show stop (E (x-step i)) (S.repath i)=E x from (S.stop_repath ..).trans (back S x i))]; exact reverse_stop ..
variable {x y : Site c} (t : S.Choices) (hb : S.prediction U t=1)
include h ht hb
private lemma hit (d : Step): travel U (E x) (downwalk S d)=1:= by
   have he i (x : Site c) : travel U (E x) (S.repath i)=1:= (prophecy S ht h (x,i) t).symm.trans (congrFun hb (x,i))
   cases d with | mk i b =>
   cases b; exact he ..
   change travel U (E x) (Lattice.reverse _)=1; rw [← show stop (E (x-step i)) (S.repath i)=E x from (S.stop_repath ..).trans (back S x i), travel_reverse,he,inv_one]

private def stretch (s : Walk):= s.flatMap (downwalk S)
omit h ht hb in
lemma path_costs (a b : Walk) : pathLength (a++b)=pathLength a+ pathLength b := by induction a with
                                                                                   | nil=> simp [pathLength]
                                                                                   | cons d a ih=> simp only [List.cons_append,pathLength, ih,add_assoc]
omit h ht hb in
private lemma costs (d : Step) : pathLength (downwalk S d)= L • (d.vec:Cover):= by
   have he (i) : pathLength (S.repath i)=L • (step i: Cover):= by rw [← zero_add (pathLength _),← summit,S.stop_repath, zero_add]
   cases d with | mk i b=>
   cases b; exact he i
   change pathLength (Lattice.reverse (S.repath i))= _ • (- _); rw [smul_neg]; exact eq_neg_of_add_eq_zero_left (by
     have hs:= reverse_stop (S.repath i) (0:Cover); rw [summit,summit,he,zero_add,add_comm] at hs; exact hs)
omit h ht hb in
lemma hike_length (d : Walk): pathLength (stretch S d) = L • pathLength d:= by
   induction d with
   | nil=> simp [pathLength, stretch]
   | cons x d ih=> rw [pathLength,show stretch S (x::d)=downwalk S x ++ stretch S d from rfl,path_costs,ih,costs,smul_add]
lemma long_anchors (d : Walk): travel U (E x) (stretch S d)=1 := by
   induction d generalizing x with
   | nil=> exact (rfl)
   | cons a d ih=> rw [show stretch S (a::d)=downwalk S a ++ stretch S d from rfl, travel_append,stop_one,hit S h ht t hb,ih,one_mul]

-- criterion even on smallest torus (one coarse site).
omit h ht hb in
lemma worth (d : Walk) (he : stop (E x) d= E y): ∃ z : Cover,pathLength d=L • z:= by
   have hp:= congrArg S.ratio.residue he; rw [target,map_add,Ratio.residue_embed,Ratio.residue_embed,zero_add, Ratio.residue_wrap] at hp
   have h (i:Axis) := ZMod.intCast_zmod_eq_zero_iff_dvd ((pathLength d) i) (L) |>.mp (congrFun hp i); choose u hu using h
   exact ⟨u, funext fun i=>by simpa only [Pi.smul_apply,nsmul_eq_mul] using (hu i)⟩
lemma follows (d : Walk) (he : stop (E x) d= E y) : travel U (E x) d=1:= by
   obtain ⟨z,h⟩:= worth S d he
   let v:=route 0 z 1; have hp:pathLength v=z:= by rw [← zero_add (pathLength _),← summit,route_end]
   rw [journey ht d (stretch S v) (E x) (by rw [hike_length,h,hp]),long_anchors S ‹_› ht t hb]

variable (F : Forest S.ratio) {u : F.Slice G}
omit h ht hb in
private lemma lives (x: Site f) : travel (F.drape u) x (F.hike x)=1 := by
   induction x using Forest.hike.induct F with
   | case1 i hi ih=>
      have hv := F.on_tree u ⟨_, (F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩⟩
      rw [Forest.hike,dif_pos hi,travel,ih,mul_one]; change (F.up i).read _ _=1
      unfold Step.read; split; exact (congrArg (·⁻¹) hv).trans (inv_one (G:=G.El)); exact hv
   | case2 i hi=> rw [Forest.hike, dif_neg hi]; rfl
lemma unique_root (he : U=F.drape u): u=1:= by
   subst U; let U:= F.drape u
   have hp (x : Site f) (d : Step): d.read U x=1:= by
       let y:=x+d.vec; let a:=F.hike x; let b:= F.hike y; let W:=Lattice.reverse a ++ (d::b)
       let X:=S.ratio.parent x; let Y:= S.ratio.parent y
       have he: stop x a=E X:= F.hike_root x
       have hS : stop (E X) (Lattice.reverse a)=x:= he ▸ reverse_stop a x
       have hg : stop (E X) W = E Y:= by unfold W; rw [stop_append,hS,stop]; exact F.hike_root y
       have hy := follows S h ht t hb W hg; unfold W at hy; rw [travel_append,hS,← he,travel_reverse,travel,lives,lives,inv_one,mul_one, one_mul] at hy; exact hy
   funext i; exact (F.off_tree u i).symm.trans (hp i.val.1 (posDir i.val.2))
end YM.Comparison.RG02.Bare
