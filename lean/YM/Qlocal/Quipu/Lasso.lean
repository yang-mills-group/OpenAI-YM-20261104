import YM.Next.STATIONARY.Level.SliceGate
import YM.Lattice.Foliation
import YM.Work.F02.Series
/-!
A cochain lift for a rooted mark uses a cover-based closed
walk, cost of its curvature (before factors of g). Shape actual transports
in group's compact normalization. Retains no-harm subset from masks.
Thin world: charge every corner, at linear length. Handles zero paths.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Lasso
open Function Filter Lattice Laurent RG Wilson Stationary
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {o:Lattice.Order} {c:Cover} {i j:Axis}
-- LHS vs RHS plaquette for ANY step shape
variable (U:CoverConfig G)
lemma shellSteps (a b:Step)(x:Cover): travel U x (oriented a b) = a.read U x * b.read U (x+a.vec) * (b.read U x * a.read U (x+b.vec))⁻¹:= by
   unfold oriented; simp only [travel, Step.vec_rev, mul_one]; rw [show x+a.vec+b.vec+-a.vec=x+b.vec by abel, show x+a.vec+b.vec=x+b.vec+a.vec by abel, Step.read_rev,Step.read_rev]; group

-- oriented price asks only the four vertices from visits
variable {B:ℝ} (A: Finset Cover)
def Paid (U:CoverConfig G)(A:Finset Cover)(t:ℝ):Prop := ∀ x:Face ℤ, (visits x.1 (square x.2.val.1 x.2.val.2)).toFinset ⊆ A → G.chord (faceValue U x)≤t
lemma square_corners' (u: Cover)(a:Step) (i:Axis):
    (visits (atFace u a (posDir i)) (square a.dir i)).toFinset={u,u+a.vec,u+a.vec+step i,u+step i}:=by
    ext v; rcases a with ⟨k,h|h⟩<;> simp only [atFace,square_corners,posDir, Bool.false_eq_true, ↓reduceIte, add_zero]
    · simp [Step.vec, eq_comm]; tauto
    simp [Step.vec]; tauto
lemma Paid.bars (h:Paid U A B)(a:Step)(x:Cover)(ht:a.dir≠i)(hv:( {x,x+a.vec,x+a.vec+step i,x+step i}:Finset Cover)⊆A): G.chord (travel U x (oriented a (posDir i)))≤ B := by
    rw [price_shift_pos G.chord U G.chord_inv (fun k g => G.chord_conj g k)]; let u:= atFace x a (posDir i)
    rcases lt_or_gt_of_ne ht with hg|hg
    · exact h (u,⟨(a.dir,i),hg⟩) (by rw [show _=((visits u (square a.dir i)).toFinset) from rfl,square_corners' _ a i]; exact hv)
    have he : (visits u (square i a.dir)).toFinset=(visits u (square a.dir i)).toFinset:= by ext; simp only [square_corners]; rw [add_right_comm u (step i) (step a.dir)]; simp; tauto
    change G.chord (travel U u (oriented (posDir a.dir) (posDir i)))≤_; rw [oriented_swap (posDir i),G.chord_inv]; exact h (u,⟨(i,a.dir),hg⟩) (he.trans (square_corners' _ _ _) ▸ hv)
lemma visits_origin (x:Cover)(w:Walk): x ∈ visits x w:= by cases w<;>simp [visits]
lemma visits_grow (w:Walk)(x:Cover)(a:Step): (visits (x+a.vec) w).toFinset⊆(visits x (a::w)).toFinset:=by intro i hi; simp only [visits,List.toFinset_cons]; exact Finset.mem_insert_of_mem hi
lemma Paid.patch (h : Paid U A B)(w:Walk)(x:Cover)(he: ∀ a∈w,a.dir≠i)(hv:(visits x w).toFinset⊆A)(hg:(visits (x+step i) w).toFinset⊆ A) :
    G.chord (travel U x w * U (stop x w,i) * (U (x,i) * travel U (x+step i) w)⁻¹) ≤ (w.length:ℝ)*B:= by
    induction w generalizing x with
    | nil => simp [travel,Lattice.stop]
    | cons a w ih=>
       let y:=x+a.vec; let T:= travel U y w * U (stop y w,i); let V:= U (y,i)*travel U (y+step i) w
       have hm : (visits y w).toFinset ⊆ A:= (visits_grow w x a).trans hv
       have hh: (visits (y+step i) w).toFinset ⊆ A:= by rw [show y+step i = x+step i+a.vec by unfold y; abel]; exact (visits_grow w ..).trans hg
       have hP:a∈a::w:= List.mem_cons_self
       have hf:= ih y (fun a ha=>he a (List.mem_cons_of_mem _ ha)) hm hh
       let q:= travel U x (oriented a (posDir i))
       have H:G.chord q ≤ B:= Paid.bars U A h a x (he a hP) (by
           rw [Finset.insert_subset_iff,Finset.insert_subset_iff,Finset.insert_subset_iff,Finset.singleton_subset_iff]
           exact ⟨hv (List.mem_toFinset.mpr (visits_origin ..)),hm (List.mem_toFinset.mpr (visits_origin ..)),hh (List.mem_toFinset.mpr (visits_origin ..)),hg (List.mem_toFinset.mpr (visits_origin ..))⟩)
       rw [show travel U x (a::w)*U (_, i)*(U (x,i)*_)⁻¹= (a.read U x*(T*V⁻¹)*(a.read U x)⁻¹)*q from ?_]; swap
       ·
         unfold q T V; rw [shellSteps]; simp only [y,travel,Step.pos_read, stop,Step.vec_pos]; rw [add_right_comm x (step i)]; group
       apply (G.chord_triangle ..).trans
       rw [G.chord_conj]; exact (add_le_add hf H).trans_eq (by simp [add_mul])
lemma stalk (x : Cover)(v w:Walk): (visits (stop x v) w).toFinset ⊆ (visits x (v++w)).toFinset:= by
    induction v generalizing x with
    | nil=> simp [stop]
    | cons a v ih=> exact (ih _).trans (visits_grow _ _ a)
lemma axes_other (i:Axis)(x:Cover) (l:List Axis) (h:i ∉ l): axisRoute 0 (x+step i) l=axisRoute 0 x l:= by
   apply axis_route_support; intro j hj; have h:j≠i:=fun hx=>h (hx ▸ hj); simp [h]

def trail (o:Lattice.Order) (x:Cover) (i: Axis):Walk:= (route 0 x o ++ [posDir i])++Lattice.reverse (route 0 (x+step i) o)
def plot (o:Lattice.Order)(x:Cover)(i:Axis):Finset Cover:= (visits 0 (route 0 x o)).toFinset∪(visits 0 (route 0 (x+step i) o)).toFinset
lemma enclose : stop (0:Cover) (trail o c i)=0:= by
   rw [trail,stop_append, stop_append,route_end]; conv_lhs=>arg 1; rw [stop,Step.vec_pos,stop,← route_end 0 (c+step i) o]
   exact reverse_stop ..
lemma carry (x : Cover)(o:Lattice.Order)(j:Axis): travel U 0 (trail o x j)= travel U 0 (route 0 x o)*U (x,j)*(travel U 0 (route 0 (x+step j) o))⁻¹:= by
    rw [trail, travel_append,travel_append,stop_append,route_end]; simp only [travel,stop,Step.vec_pos, Step.pos_read,mul_one]; conv_lhs=>arg 2; arg 2; rw [← route_end 0 (x+step j) o]
    rw [travel_reverse]
lemma trail_length : (trail o c i).length ≤ 2*size c+2:= by
   unfold trail; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,Lattice.reverse,List.length_map,List.length_reverse, Stationary.route_length,sub_zero]; have hv:=size_add c (step i); rw [show size (step i:Cover)=1 by simp [size,step,Pi.single_apply,apply_ite Int.natAbs]] at hv; omega
lemma visit_charge (x:Cover)(w:Walk): (visits x w).length=w.length+1:= by induction w generalizing x <;>simp [visits, *]
lemma sparsity : (plot o c i).card≤2*size c+3 := by
    unfold plot; refine (Finset.card_union_le ..).trans ((add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)).trans ?_)
    simp only [visit_charge, Stationary.route_length, sub_zero]; have hv:=size_add c (step i); rw [show size (step i:Cover)=1 by simp [size,step,Pi.single_apply,apply_ite Int.natAbs]] at hv; omega
lemma done (x:Cover)(w:Walk): stop x w∈visits x w := by induction w generalizing x<;>simp [stop,visits, *]
-- local even if x and end sampled at cut points
lemma trailLocal (o:Lattice.Order)(x:Cover)(i:Axis) : LocalOn ↑(plot o x i) fun A:CoverConfig G=> travel A 0 (trail o x i):= by
   intro A V h; let a:= (visits (0:Cover) (route 0 x o)).toFinset; let b:= (visits (0:Cover) (route 0 (x+step i) o)).toFinset; have ha:a⊆plot o x i:= Finset.subset_union_left; have hb:b⊆plot o x i:= Finset.subset_union_right
   change travel _ _ _=travel _ _ _
   rw [carry A,carry V, show travel A 0 (route 0 x o)=travel V 0 (route 0 x o) from travel_local (0:Cover) (route 0 x o) A V (fun e he hn=> h e (ha (List.mem_toFinset.mpr he)) (ha (List.mem_toFinset.mpr hn))),show travel A 0 (route 0 (x+step i) o)=travel V 0 (route 0 (x+step i) o) from travel_local (0:Cover) (route 0 (x+step i) o) A V (fun e he hn=>h e (hb (List.mem_toFinset.mpr he)) (hb (List.mem_toFinset.mpr hn))),h (x,i) (ha (List.mem_toFinset.mpr ?_)) (hb (List.mem_toFinset.mpr ?_))]
   · have he:=done 0 (route 0 x o); rw [route_end] at he; exact he
   have he:= done 0 (route 0 (x+step i) o); rw [route_end] at he; exact he
-- connector between x-parts on shifted paths. one chord per step
lemma trail_price (ht:0 ≤ B)(h: Paid U (plot o c i) B) : G.chord (travel U 0 (trail o c i))≤ B*size c := by
    have hv:i∈ allAxes o:=List.mem_map.mpr ⟨o.symm i,by simp,by simp⟩
    obtain ⟨a,b,he⟩:= List.append_of_mem hv
    have hz: (allAxes o).Nodup:= (List.nodup_finRange _).map o.injective
    rw [he] at hz
    obtain ⟨ha,hb,hu⟩:=List.nodup_append.mp hz
    have hk : i∉a:= fun h=> hu i h i (by simp) rfl
    have hh: i∉b:=List.nodup_cons.mp hb|>.1
    let p:=axisRoute 0 c a; let r:=straight i (c i); let w:=axisRoute 0 c b
    let r':=straight i (c i+1)
    have h₁: route 0 c o=(p++r)++w:= by unfold route; rw [he, axisRoute_append]; simp [p,r,w,axisRoute]
    have h₂: route 0 (c+step i) o=(p++r')++w:= by unfold route; rw [he,axisRoute_append,show axisRoute _ _ (i::b)= _ ++ axisRoute 0 (c+step i) b from rfl,axes_other _ _ a hk,axes_other _ _ b hh]; simp [p,r',w] -- rfl?
    let y:=stop (0:Cover) p; let x:= stop y r
    have hx: stop y r'= x+step i:=by unfold r' x r; rw [straight_stop,straight_stop,add_smul,one_smul]; abel
    have hp : stop x w=c:= by rw [← show stop 0 (p++r)=x from stop_append .., ← stop_append, ← h₁, route_end]
    have hW : ∀ e∈w,e.dir≠i:= by
        intro e he; obtain ⟨j,hj,hl⟩:= List.mem_flatMap.mp he; unfold straight at hl
        have hz := (List.mem_replicate.mp hl).2; change e ∈ List.replicate _ _ at hl
        intro hu; apply hh; exact ((congr_arg Step.dir hz).symm.trans hu ▸ hj)
    have hy : (visits x w).toFinset⊆plot o c i:= le_trans (b:=(visits (0:Cover) (route 0 c o)).toFinset) (by rw [h₁]; exact (show stop 0 (p++r)=x from stop_append ..) ▸ stalk 0 (p++r) w) Finset.subset_union_left
    have hg : (visits (x+step i) w).toFinset⊆plot o c i:= le_trans (b:=(visits (0:Cover) (route 0 (c+step i) o)).toFinset) (by rw [h₂]; exact (show stop 0 (p++r')=x+step i by rw [stop_append]; exact hx) ▸ stalk 0 (p++r') w) Finset.subset_union_right
    have hC:= Paid.patch U _ h w x hW hy hg; rw [hp] at hC
    have hc:travel U y r'=travel U y r*U (x,i):= by unfold x r' r; rw [straight_stop]; exact carry_succ ..
    let X:= travel U x w*U (c,i)*(U (x,i)*travel U (x+step i) w)⁻¹
    rw [show travel U 0 (trail o c i)= travel U 0 (p++r)*X*(travel U 0 (p++r))⁻¹ from ?_, G.chord_conj]
    · have he : w.length≤ size c:= by
         have he : (route 0 c o).length=size c:= by rw [route_length,sub_zero]
         rw [h₁,List.length_append] at he; omega
      exact hC.trans ((mul_comm _ B|>.le).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast he) ht))
    unfold X; rw [carry U,h₁,h₂,travel_append,travel_append U _ (p++r') w,stop_append, stop_append _ p r']; rw [show stop (0:Cover) p=y from rfl,hx, show stop y r=x from rfl,travel_append _ _ p r',show stop 0 p=y from rfl,hc,travel_append U 0 p r, show stop 0 p=y from rfl]; group
end YM.Qlocal.Quipu.Lasso
