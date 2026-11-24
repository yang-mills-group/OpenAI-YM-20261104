import YM.SchemeRG11.Cover.Breathe
import YM.Pert.First.Completion
/-! Ward test on native chart, for arbitrary link walks. Sign notation:
 `march` **negative** gradient connection parameter compared to Orb.grad
 gauge parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Bark
open Lattice Function Filter Asymptotics Haze Pert
open scoped Classical ContDiff Matrix.Norms.Frobenius
variable {L : Type*} [AddCommGroup L] [One L] {G : Gauge}

abbrev trunk (G:Gauge)(L:Type*) := Links L G.Color
abbrev unroll (v : trunk G L)(r:ℝ) : Links L G.El:= fun e=> G.lieExp (r • v e)
def heel (d:Step)(x:Four L)(v : trunk G L):= if d.neg then -(v (d.used x)) else v (d.used x)
def mileage (x:Four L) (s:Walk) (A:trunk G L): G.Color:= match s with
| [] => 0
| d::s => heel d x A + mileage (x+d.vec) s A
def cohort (x:Four L) (s:Walk) (A B:trunk G L): G.Color:= match s with
| [] => 0
| d::s=> cohort (x+d.vec) s A B + G.ad (heel d x A) (mileage (x+d.vec) s B)
def leap (x:Four L) (s:Walk) (A:trunk G L):= cohort x s A A
lemma heel_speed (x:Four L)(d:Step)(A:trunk G L)(t:ℝ): G.mat (d.read (unroll A t) x) = First.glow (heel d x A) t:=by
 unfold heel Step.read; split
 · apply First.glow_inv
 rfl
lemma arc (x:Four L)(s:Walk)(A:trunk G L): First.Tried (fun t:ℝ=> G.mat (travel (unroll A t) x s)) (mileage x s A) (leap x s A):=by
 unfold leap
 induction s generalizing x with
 | nil=> simp only [mileage,cohort,travel,G.mat_one]; rw [show (fun t:ℝ=>(1:G.Mat))=First.glow (0:G.Color) by funext t; simp [First.glow]]; exact (First.glow_tried (G:=G) (v:=0))
 | cons d s ih=> simp only [mileage,cohort,travel,G.mat_mul, heel_speed]; simpa only [zero_add] using (First.glow_tried (v:=heel d x A)).product (ih (x+d.vec))
lemma decode_color(v:G.Color): First.recoverL G (G.colorMat v)=v:=by
 change G.projectColor ((1/2:ℝ) • (G.colorMat v-star (G.colorMat v)))=_
 rw [G.colorMat_skew,sub_neg_eq_add,smul_add,←add_smul,show 1/2+(1/2:ℝ)=1 from by norm_num,one_smul,G.project_colorMat]
lemma log_arc(x:Four L)(s:Walk)(A:trunk G L): iteratedDeriv 1 (fun t:ℝ=> G.curvature (travel (unroll A t) x s)) 0=mileage x s A ∧ iteratedDeriv 2 (fun t:ℝ=> G.curvature (travel (unroll A t) x s)) 0=leap x s A:=by
 simp_rw [First.recover_group]; let F t:=G.mat (travel (unroll A t) x s); have hp:= arc x s A
 refine ⟨?_,hp.decode_second⟩; rw [iteratedDeriv_one]; obtain ⟨z,hz,hq,-⟩:= hp.slope_eq; exact ((First.recoverL G).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hq 0)).deriv.trans (by rw [hz]; exact decode_color _)

def turn (x: Lattice.Walk)(i j:Axis):Lattice.Walk:= (x++ Lattice.square i j) ++ Lattice.reverse x
lemma turn_stop (x : Four L)(s:Walk)(i j:Axis): stop x (turn s i j)=x:=by simp only [turn,stop_append,square_stop,reverse_stop]
lemma turn_path (x : Four L)(s:Walk)(i j:Axis)(U : Links L G.El): Bare.plateU U x s i j=G.curvature (travel U x (turn s i j)):=by rw [turn,travel_append,travel_append,stop_append, square_stop,travel_reverse,G.curvature_conjugate];rfl

def ascent (e: Four L→ G.Color): trunk G L:=fun l=> e (l.1+step l.2)-e l.1
def spur (e: Four L→ G.Color)(A:trunk G L): trunk G L:= fun l=> G.ad (A l) (e (l.1+step l.2)+e l.1)
lemma heel_up(x:Four L)(d:Step)(e:Four L→G.Color): heel d x (ascent e)=e (x+d.vec)-e x:=by
 cases d with | mk i b=> cases b <;> simp [heel,ascent,Step.used,Step.vec, sub_eq_add_neg]
lemma heel_stamp(x:Four L)(d:Step)(e:Four L→G.Color)(A:trunk G L): heel d x (spur e A)= G.ad (heel d x A) (e (x+d.vec)+e x):=by
 cases d with | mk i b=> cases b <;> simp [heel,spur,Step.used,Step.vec,sub_eq_add_neg]; abel
lemma mile_stop (x : Four L)(s:Walk)(e:Four L→G.Color): mileage x s (ascent e)=e (stop x s) - e x:=by
 induction s generalizing x with
 | nil=> simp [mileage,stop]
 | cons d s ih => rw [mileage,ih,heel_up,stop]; abel
lemma antisym (a b:G.Color): G.ad a b=-(G.ad b a):=by apply G.colorMat_injective; simp
lemma test (x: Four L)(s:Walk)(A:trunk G L)(e:Four L→G.Color) :
 cohort x s (ascent e) A + cohort x s A (ascent e) + mileage x s (spur e A) = G.ad (mileage x s A) (e (stop x s) + e x):=by
 induction s generalizing x with
 | nil=> rw [mileage,cohort,cohort,mileage,map_zero]; simp
 | cons d s ih=>
   let y : Four L:=x+d.vec;let z:=stop y s
   let K:= heel d x A; let U:=mileage y s A
   let Q:= ascent e
   rw [cohort,cohort,mileage,heel_up,mile_stop,heel_stamp,mileage,stop]
   change (cohort y s Q A + G.ad (e y - e x) U) + (cohort y s A Q + G.ad K (e z-e y)) + (G.ad K (e y+e x)+_) = _
   have he:=ih y; change cohort y s Q A + cohort y s A Q + mileage y s _ = G.ad U (e z+e y) at he
   have ht : G.ad (e y-e x) U = G.ad U (e x-e y):=by rw [antisym (e y-e x),← map_neg,neg_sub]
   change _+(_+mileage y s _) = G.ad (K+U) (e z+e x)
   rw [ht,show mileage y s (spur e A)=_ from eq_sub_of_add_eq' he]
   simp only [map_add, map_sub, LinearMap.add_apply]; abel

lemma heel_add (d:Step)(x:Four L)(A B:trunk G L): heel d x (A+B)=heel d x A+heel d x B:=by
 unfold heel; split; · simp; abel
 rfl
lemma heel_smul (d:Step)(x:Four L)(t:ℝ)(A:trunk G L): heel d x (t • A)=t • heel d x A:=by
 unfold heel; split; · simp
 rfl
lemma mileage_add (x:Four L)(s:Walk)(A B:trunk G L): mileage x s (A+B)=mileage x s A+mileage x s B:=by induction s generalizing x with | nil=> simp [mileage] | cons d s ih=>rw [mileage,heel_add,ih,mileage,mileage]; abel
lemma mileage_s (x:Four L)(s:Walk)(A:trunk G L)(t:ℝ): mileage x s (t • A)=t • mileage x s A:=by induction s generalizing x with | nil=> simp [mileage] | cons d s ih=> rw [mileage,heel_smul,ih,mileage,smul_add]
lemma co_add (x:Four L)(s:Walk)(A B C:trunk G L): cohort x s (A+B) C=cohort x s A C+cohort x s B C:=by induction s generalizing x with | nil=> simp [cohort] | cons d s ih=> rw [cohort,heel_add,ih,cohort,cohort,map_add,LinearMap.add_apply]; abel
lemma co_add' (x:Four L)(s:Walk)(A B C:trunk G L): cohort x s C (A+B)=cohort x s C A+cohort x s C B:=by induction s generalizing x with | nil=> simp [cohort] | cons d s ih=> rw [cohort,mileage_add,ih,cohort,cohort,map_add]; abel
lemma co_s (x:Four L)(s:Walk)(A C:trunk G L)(t:ℝ): cohort x s (t • A) C=t • cohort x s A C:=by induction s generalizing x with | nil=>simp [cohort] | cons d s ih=> rw [cohort,heel_smul,ih,cohort,map_smul, LinearMap.smul_apply,smul_add]
lemma co_s' (x:Four L)(s:Walk)(A C:trunk G L)(t:ℝ): cohort x s C (t • A)=t • cohort x s C A:=by induction s generalizing x with | nil=>simp [cohort] | cons d s ih=> rw [cohort,mileage_s,ih,cohort,map_smul,smul_add]
end YM.SchemeRG11.Bark
