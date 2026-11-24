import YM.MSbar.Scale.Table
import YM.MSbar.Counter.Symbol

/-! Ray coordinates on the allowed hyperplane. Scale only momenta. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale
open Dim Symbol Domain Diagram Super Loops Function Set Filter Counter
open scoped Topology BigOperators Classical ContDiff MeasureTheory
variable {C:Type}{W: Edition C}{m j:ℕ}{U:Set ℂ}{d:Bit} {f:Vertex C}{w:Words C m}{F:Functionals C} {r t:ℝ}

def drag (t:ℝ)(w:Words C m):Words C m:=w.map (fun a=>(a.1,t • a.2))
@[simp] lemma drag_app (x y:Words C m) (t:ℝ): drag t (x++y)=drag t x++drag t y:=List.map_append ..
@[simp] lemma drag_cons (a:Letter C m)(t:ℝ)(x): drag t (a::x)=(a.1,t • a.2)::drag t x:=rfl
@[simp] lemma drag_skin (t:ℝ)(w: Words C m): skin (drag t w)=skin w:=by simp [skin,drag];rfl
@[simp] lemma drag_pat (x:Words C m) (t:ℝ) : oddity (lift (W.binary m)) (drag t x)=oddity (lift (W.binary m)) x:=by rw [oddity,oddity,drag,List.map_map];rfl
@[simp] lemma drag_one : drag 1 w=w:=by simp [drag]
@[simp] lemma drag_bal : channel (drag t w)= t • channel w:= by induction w with | nil=> simp [drag] | cons a t ih=> simp [channel_cons,ih,smul_add]
@[simp] lemma drag_twice : drag r (drag t w)=drag (r*t) w:=by simp only [drag, List.map_map]; simp [Function.comp,smul_smul]

-- zero fallback to avoid offsite nonneutral jump at λ=0
def ray (f:Vertex C)(x:Words C m)(s:ℝ) : ℂ:= if channel x=0 then f m (drag s x) else 0
lemma along (h: Cell W d f)(s:ℝ): Cell W d (fun i x=>ray f x s):=by
   refine ⟨fun ⦃i j⦄ L x=>?_,fun n x hx=>?_,fun i t p u v=>?_,fun i=>⟨fun u a b v=>?_,fun x hx=>?_⟩⟩
   · have hr: drag s ((line C).move L x)=(line C).move L (drag s x):=by induction x with | nil=> simp [drag] | cons c x ih=>rw [work,drag_cons,ih,drag_cons,work,map_smul]
     simp only [ray,quiet_move,map_eq_zero_iff _ (taxi_inj L),hr,h.nature L (drag s _)]
   · simp [ray,hx]
   · simp only [ray, channel_plus, channel_cons]; by_cases H:channel u+(p+channel v)=0
     · simp only [H,↓reduceIte,drag_app,drag_cons]; exact h.color ..
     simpa only [H,↓reduceIte] using! (Dim.One.zero (X:=Hat i) (p:=W.vector t))
   · simp only [ray,channel_plus,channel_cons,drag_app,drag_cons]; rw [add_left_comm a.2 b.2, (h.sign i).commute]; split_ifs; rfl; simp
   unfold ray; split_ifs; apply (h.sign i).shape; simpa; rfl
lemma ray_center (hf:Cell W d f) : ray f w 1=f m w := by rcases eq_or_ne (channel w) 0 with H|H; simp [ray,H]; simp [ray,H,hf.quiet m w H]
lemma arms (hv:channel w=0): ray f (drag t w)=Flight.pull t (ray f w):=by ext u; simp [Flight.pull,ray,hv]
-- smoothness on rays & their variation in plots
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma Ray_plot {p:E→ℝ}{v:E→Words C m}(hp:p.HasTemperateGrowth)(h:Domain.Plot E C m v): Domain.Plot E C m (fun x=>drag (p x) (v x)) := by
   induction h with
   | empty=> exact Plot.empty
   | cons a t u ht hu _ ih=> exact Plot.cons a t _ ht (hp.smul hu) ih
lemma Arm {v:E→Words C m}(h:(arena C).plot v){r:E→ℝ}(hr: r.HasTemperateGrowth): (arena C).plot (fun x=>drag (r x) (v x)):=⟨Ray_plot hr h.1, fun x=> by rw [Domain.Balanced, drag_bal,h.2 x,smul_zero]⟩
lemma bright_ray (hf: Domain.Full U j W d F)(hp:IsOpen U){v:E→Words C m}(h:(arena C).plot v): Bet U j (fun p:ℂ × (E × ℝ)=> ray (F p.1) (v p.2.1) p.2.2):= by
   have he:=(arena C).views (p:=Prod.fst (α:=E) (β:=ℝ)) h tame_projL
   refine (hf.licensed.ev _ _ (Arm he tame_projR)).congr hp ?_; intro z hz x; rw [ray, if_pos (h.2 x.1)]; rfl
lemma great_ray (hf: Live W d f)(v:Words C m): Flight.Great (ray f v) := by
    by_cases H: channel v=0
    · have he:= hf.licensed.ev _ (fun x:ℝ=> drag x v) (Arm (r:=id) (v:=fun _=>v) (by exact ⟨Plot.cte v,fun _=>H⟩) (by fun_prop))
      rw [show ray f v=(fun t=>f m (drag t v)) from funext fun x=>by simp [ray,H]]; exact (he.cost.slice (mem_univ 0)) -- eta
    have he : ray f v=(0:Flight.Vec):=funext fun t=>by simp [ray,H]
    rw [he];exact HasTemperateGrowth.const 0
lemma ray_scale (c:ℂ)(x:Words C m)(f:Vertex C): ray (c•f) x=c • ray f x := by funext s; unfold ray; by_cases h:channel x=0 <;> simp [h]
lemma ray_add (x:Words C m)(f g:Vertex C): ray (f+g) x=ray f x+ray g x:= by funext s; unfold ray; by_cases h:channel x=0 <;> simp [h]
@[simp] lemma ray_zero (x:Words C m): ray 0 x=0:=by ext; simp [ray]
end YM.MSbar.Scale
