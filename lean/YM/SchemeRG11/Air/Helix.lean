import YM.SchemeRG11.Air.Fly
import YM.SchemeRG11.Banner.Ruin
/-! TVariable moments through weights. AIR profile evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook
open Labels Long
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T:Align.Itinerary}{R r:ℝ}
abbrev Falls(G:Gauge):= ℕ→ Shaft G →ℝ
def Act (T:Align.Itinerary)(R:ℝ)(f:Slate):Prop:=∀ (s:Fliers)(p:E4),‖p‖<2*R→∀ v:ℕ → Cover,Along T v p→ Finishes (fun i=>T.gap i ^ (-(s.card+1:ℤ))*fleet s (f i) (v i))
def ribbon(F:Falls G)(u: G.ColorIndex):Waves:=fun i a=> Long.element (F i) a u
structure Blue (T:Align.Itinerary)(R:ℝ)(F:Falls G):Prop where
 shore (u): brittle T R (ribbon F u)
 shape (u): keeps T R (ribbon F u)
 came (u j): Act T R (fun i=>ribbon F u i j)
namespace Blue
variable {F A:Falls G}
lemma zero :Blue T R (0:Falls G):=by
 refine ⟨fun u j s=> ?_, fun u=>?_,fun u j s p h v ht=>?_⟩
 · have he:ribbon (0:Falls G) u=0:=rfl
   rw [he]; unfold dove; simp only [Pi.zero_apply,map_zero]; apply Wall.zero
 · rw [show ribbon (0:Falls G) u=0 from rfl]; exact Eventually.of_forall fun i x h=> ⟨congrFun (map_zero Flock.dive) _,fun _=> congrFun (map_zero lap) _⟩
 rw [show ribbon (0:Falls G) u=0 from rfl]; simp only [Pi.zero_apply,map_zero,mul_zero]; exact Finishes.const _
lemma add(h:Blue T R F)(b:Blue T R A):Blue T R (F+A):=by
 have H(a:G.ColorIndex): ribbon (F+A) a=ribbon F a + ribbon A a:=rfl
 refine ⟨fun u a s=>?_,fun u=>?_,fun u a s p he v z=>?_⟩
 · convert (h.shore u a s).add (b.shore u a s) using 1; funext i; unfold dove; simp only [H,Pi.add_apply,map_add]
 · filter_upwards [h.shape u,b.shape u] with i hi hk x hx; simp only [H,map_add, Pi.add_apply,(hi _ hx).1,(hi _ hx).2,(hk _ hx).1,(hk _ hx).2,add_zero,and_self, forall_const]
 simp only [H,Pi.add_apply,map_add,mul_add]; exact (h.came u a s p he v z).add (b.came u a s p he v z)
lemma scale(h:Blue T R F)(c:ℝ): Blue T R (c • F):=by
 have H(a:G.ColorIndex): ribbon (c • F) a=c • ribbon F a:=rfl
 refine ⟨fun u a s=> ?_,fun u=>?_,fun u a s p he v z=>?_⟩
 · convert (h.shore u a s).pay_s c using 1; funext i; unfold dove; simp only [H,Pi.smul_apply,map_smul]
 · filter_upwards [h.shape u] with i hi x hx; simp only [H,Pi.smul_apply,map_smul,(hi _ hx).1, (hi _ hx).2,smul_zero, true_and,forall_const]
 simp only [H,Pi.smul_apply,map_smul,smul_eq_mul,mul_left_comm _ c]; exact (Finishes.const _).mul (h.came u a s p he v z)
lemma sum {I:Type*}(p:I→Falls G)(s:Finset I)(h:∀i∈s,Blue T R (p i)):Blue T R (∑ i∈s,p i):=by
 induction s using Finset.induction_on with
 | empty=>rw [Finset.sum_empty];exact zero
 | insert i s hi ih=>rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun i hi=> h i (by simp [hi]))
end Blue
lemma spring {F:Falls G}(h:Blue T R F)(m:ℕ)(u:G.ColorIndex)(hR:R>0):Rolling T m (ribbon F u):=by
 intro a s hs; exact h.came u a s 0 (by rw [norm_zero]; positivity) _ (World.Along.base 0)
-- scaled Taylor parameters, Finishes coordinate after dividing by slot weight
def shapeV (T:Align.Itinerary)(c:ℕ→ Sky G n→ℝ):Falls G:=fun i=>cant (lump (fun z=>T.gap i ^ ((inkAge z:ℕ):ℤ)*c i z))
lemma rib (c: ℕ→ Sky G n→ℝ) (T: Align.Itinerary)(i:ℕ)(u:G.ColorIndex): ribbon (shapeV T c) u i= ∑ z: Feather n,(T.gap i ^ ((degree z:ℕ):ℤ)*c i (z,u)) • finch z:=by
 funext a j
 unfold shapeV lump ribbon; simp only [Fintype.sum_prod_type]; unfold Long.element cant; rw [Finset.sum_apply]; simp only [WithLp.ofLp_sum, Finset.sum_apply]; apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_eq_single u]; change (_*(finch k a j*(unitColor G u u))) = _*finch k a j; rw [unitPaint]; simp [inkAge]
 · intro b _ hb; change (_:ℝ)*(finch k a j*unitColor G b u)=0; simp [unitPaint,Ne.symm hb]
 simp
lemma cloudNet {F:Falls G}(n:ℕ)(h:Blue T R F)(hr:R>0): ∃ c : ℕ→ Sky G n→ℝ, (∀p,Finishes (fun i=> c i p)) ∧∀ u:G.ColorIndex,∀a:Axis,∀s:Fliers, Local T R ((n:ℤ)+1) ((n:ℤ)-s.card) (fun i=> fleet s (ribbon F u i a - ribbon (shapeV T c) u i a)):=by
 choose g H X using fun u=> insured n hr (h.shore u) (h.shape u) (spring h n u hr)
 choose b B Q using fun u=> lift_off n (n:=n) (fun i=>(g u i).property) (H u) le_rfl
 let t (i:ℕ)(p:Sky G n):=b p.2 i p.1; refine ⟨t,fun p=> B _ _, fun u a s=>?_⟩
 have he(i:ℕ) : ribbon (shapeV T t) u i= (g u i).val:= (rib t T i u).trans (Q u i).symm
 simp_rw [he]; exact X u a s

end YM.SchemeRG11.Air
