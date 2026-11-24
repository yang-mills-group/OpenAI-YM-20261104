import YM.Qlocal.Quipu.Lasso
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Clover
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Lasso
open Function Filter Lattice Laurent RG Wilson Stationary
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {o:Lattice.Order} {c:Cover} {i j:Axis} {n:Side} {t:ℝ}
-- A concatenated walk visits the first walk's sites and the sites reached from its endpoint by the second walk.
lemma corners_join (y x:Cover)(b c:Walk): y ∈ visits x (b ++ c) ↔ y∈ visits x b ∨ y ∈ visits (stop x b) c := by
   induction b generalizing x with
   | nil=> simp only [visits,stop,List.nil_append,List.mem_singleton]
           exact or_iff_right_of_imp (fun h=> h.symm ▸ by cases c<;>simp [visits]) |>.symm
   | cons _ _ ih=> simp only [List.cons_append,visits,stop,List.mem_cons,ih, or_assoc]
lemma corners_previous (w:Walk)(x y:Cover): y ∈ visits (stop x w) (Lattice.reverse w) ↔ y∈ visits x w:= by
   induction w generalizing x with
   | nil=> simp [Lattice.reverse,stop]
   | cons a w ih=>
     simp only [Lattice.reverse,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,stop]
     change y ∈ visits _ (Lattice.reverse w ++ _) ↔ _
     rw [corners_join,ih,reverse_stop];simp only [visits,List.mem_cons,List.not_mem_nil, or_false];
     have he (a:Lattice.Step): a.rev.vec (R:=ℤ)= -a.vec := Step.vec_rev ..
     rw [he];simp only [add_neg_cancel_right]
     have hz : x+a.vec∈visits (x+a.vec) w:= by cases w <;>simp [visits]
     have hp : y=x+a.vec → y∈visits (x+a.vec) w:=by intro h; rwa [h]
     itauto
lemma corners_torus (w:Walk)(x:Cover)(o : Site n): visits (wrap n x+o) w=(visits x w).map (fun y=>wrap n y+o):= by
   induction w generalizing x with
   | nil=> simp [visits]
   | cons a w ih=> simp only [visits, List.map_cons, ← ih,map_add,wrap_vec,add_right_comm _ o]

open Finset
abbrev bent (c:Site n) (i:Cover):= wrap n i+c
abbrev aperture (w:Walk):= (visits (0:Cover) w).toFinset
abbrev Crown (w:Walk)(o:Site n):= (aperture w).image (bent o)
lemma trail_plot (y:Cover)(w:Lattice.Order)(i:Axis): aperture (trail w y i)=plot w y i:= by
   ext p; simp only [aperture, plot,mem_union,List.mem_toFinset,trail,corners_join,stop_append,route_end];
   let A:= route 0 y w; let B:=route 0 (y+step i) w; have hm:p∈visits (stop y [posDir i]) (Lattice.reverse B) ↔ p∈ visits 0 B:= by rw [show stop y [posDir i]=stop 0 B from (route_end ..).symm]; exact corners_previous ..
   rw [hm]; have hx:y ∈ visits 0 A:= (show stop 0 A=y from route_end ..) ▸ done 0 A; have he: y+step i∈ visits 0 B:= (show stop 0 B=y+step i from route_end ..) ▸ done 0 B; change ((p∈visits 0 A ∨ p∈ visits y [posDir i]) ∨ p ∈ visits 0 B) ↔ (p∈visits 0 A ∨ p∈visits 0 B); simp only [visits,List.mem_cons,List.not_mem_nil,or_false,Step.vec_pos]; aesop
lemma found_crown (w: Walk)(o:Site n) : Crown w o=(visits o w).toFinset:= by
 ext i; simp only [Crown,aperture, Finset.mem_image, List.mem_toFinset]; rw [show visits o w=(visits 0 w).map (bent o) from (by simpa [bent] using (corners_torus w 0 o))]; exact List.mem_map.symm
lemma floor_st (o:Site n)(w:Walk): stop o w= bent o (stop (0:Cover) w):= by
    have he(x:Cover): stop (wrap n x+o) w= wrap n (stop x w)+o:= by induction w generalizing x with | nil=>rfl | cons a w ih=> simp only [stop,← ih,map_add,wrap_vec,add_right_comm _ o]
    simpa only [map_zero,zero_add] using he 0
lemma encover (o: Site n)(w:Walk) (X: Finset Cover)(x:Config G n)(h: Healthy t (X.image (bent o)) x): Paid (expandAt o x) X t:= by
  intro i hi; let s:Face (Per n):=(wrap n i.1+o,i.2); unfold faceValue; rw [travel_at]; by_contra! he
  have hf: wrap n i.1+o∈ flags t x:=(flags_spec ..).mpr ⟨s, List.mem_toFinset.mpr (by unfold s; simp [square,visits]), he⟩; exact Finset.disjoint_left.mp h (Finset.mem_image_of_mem _ (hi (List.mem_toFinset.mpr (visits_origin ..)))) hf
-- use on sparse/align hulls. preserve coverage budget 1/B; reads carry_T all even winding
structure Wand (G:Gauge) where
   tour : Walk
   range : ℕ
   stop : Lattice.stop (0:Cover) tour=0
   prosperity : ∀ (t:ℝ) (U:CoverConfig G), 0≤t→ Paid U (aperture tour) t→ G.chord (travel U 0 tour)≤ t*range

namespace Wand
noncomputable def curvy (w:Lattice.Order)(z:Cover)(a:Axis): Wand G:= ⟨trail w z a,size z,enclose,fun t U ht h=>(trail_price U ht ((trail_plot z w a) ▸ h))⟩
def squarely (s : Slot) : Wand G := {
  tour:= Work.F02.slotWalk s
  range:= 1
  stop:= by unfold Work.F02.slotWalk; rw [stop_append,stop_append,square_stop, reverse_stop]
  prosperity:= by intro t U ht h; unfold Work.F02.slotWalk at *; rw [travel_append, travel_append,stop_append,square_stop,travel_reverse,G.chord_conj]; push_cast; rw [mul_one]; apply h (Lattice.stop (0:Cover) s.walk,s.plaq); intro i hi; exact List.mem_toFinset.mpr ((corners_join ..).mpr <| Or.inl ((corners_join ..).mpr (Or.inr (List.mem_toFinset.mp hi)))) }
noncomputable def seedless (G:Gauge): Wand G:= ⟨[],0,rfl, fun t _ _ _=>by simp [travel]⟩
instance : Inhabited (Wand G):=⟨seedless G⟩
variable (A:Wand G)(U:Config G n)
lemma basis_z (o:Site n) : Lattice.stop o A.tour=o:= by rw [floor_st,A.stop,bent,map_zero,zero_add]
lemma ballot (o:Site n)(ht:0≤t)(hy:Healthy t (Crown A.tour o) U): G.chord (travel U o A.tour) ≤ t*A.range:= by
 have hv:=A.prosperity t (expandAt o U) ht (encover o A.tour _ U hy); simpa only [travel_at,map_zero,zero_add] using hv
end Wand
end YM.Qlocal.Quipu.Lasso
