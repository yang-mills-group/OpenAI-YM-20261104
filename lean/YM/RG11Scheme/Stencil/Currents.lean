import YM.RG11Scheme.Mesh.Tolls

/-! Exterior equations satisfied by cover arms into any horizontal linear slot. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Stencil
open Filter Lattice Function Maxwell Pert Pert.Cellular Mesh
open scoped BigOperators Classical
abbrev link := Edge Cover
abbrev Bond (G:Gauge) := link → G.Color
abbrev Dual (G:Gauge) := Module.Dual ℝ (Bond G)

variable {G:Gauge} {E : Type} [AddCommGroup E]

def gradient (ε:Cover → E) (l:link) := ε l.1-ε (l.1+step l.2)
def diverge (U : link→ E) (x : Cover) := ∑ i:Axis,(U (x,i)-U (x-step i,i))
def quake (f:Cover → E) (x:Cover) := ∑ i:Axis,(f (x+step i)+f (x-step i)-2 • f x)
def curl (U:link→ E) (x:Cover) (i j:Axis) := U (x,i)+U (x+step i,j)-U (x,j)-U (x+step j,i)
def starCurl (U:link→ E) (x:Cover) (i:Axis) := ∑ j:Axis,(curl U x i j-curl U (x-step j) i j)
theorem radiant (U:link→ E) (x:Cover) (i:Axis) : starCurl U x i= -(quake (fun z=> U (z,i)) x) - gradient (diverge U) (x,i) := by
   unfold starCurl quake gradient diverge
   rw [←Finset.sum_neg_distrib,← Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
   refine Finset.sum_congr rfl (fun k _=>?_)
   simp only [curl,two_smul]; rw [sub_add_cancel, show x+step i-step k=x-step k+step i by abel]; abel
lemma closed (ε:Cover → E) (x:Cover) (i j) : curl (gradient ε) x i j=0 := by unfold curl gradient; rw [add_right_comm x];abel

variable (c:G.ColorIndex)
def node (u:G.Color) (l:link) : Bond G := fun k=> if k.2=l.2 then coverLine (k.1-l.1) • u else 0
def ray : Dual G→ₗ[ℝ] Bond G := LinearMap.pi (fun l=> ∑ i:G.ColorIndex, LinearMap.toSpanSingleton ℝ G.Color (unitColor G i) ∘ₗ (LinearMap.applyₗ ..) (node (unitColor G i) l))
def key (u : G.Color) (l:link) : Bond G := fun k=> if k=l then u else 0
def current : Dual G→ₗ[ℝ] Bond G := LinearMap.pi (fun l=> ∑ i:G.ColorIndex, LinearMap.toSpanSingleton ℝ G.Color (unitColor G i) ∘ₗ (LinearMap.applyₗ ..) (key (unitColor G i) l))
private lemma colors (f : G.ColorIndex→ℝ) : (∑ v, f v • unitColor G v) c=f c := by
   rw [WithLp.ofLp_sum,Finset.sum_apply]; unfold unitColor; simp
lemma ray_one (A:Dual G) (l:link) : ray A l c=A (node (unitColor G c) l) := by
   unfold ray; rw [LinearMap.pi_apply,LinearMap.sum_apply]; exact colors ..
lemma current_one (A:Dual G) (l:link) : current A l c=A (key (unitColor G c) l) := by unfold current; rw [LinearMap.pi_apply,LinearMap.sum_apply]; exact colors ..
lemma sum_key (u:G.Color) (l) : ∑ i:G.ColorIndex, u i • key (unitColor G i) l = key u l := by funext k; by_cases hk:k=l <;> simp [Finset.sum_apply, key,hk]; exact Pert.Triangle.sum_color _
lemma sum_node (u:G.Color) (l) : ∑ i:G.ColorIndex, u i • node (unitColor G i) l = node u l := by
   funext k; by_cases hk:k.2=l.2 <;> simp [Finset.sum_apply, node,hk]; simp only [smul_comm _ (coverLine _),← Finset.smul_sum, Pert.Triangle.sum_color]
lemma ray_eval (A:Dual G)(u:G.Color) (l): inner ℝ u (ray A l) = A (node u l) := by
    rw [PiLp.inner_apply,←sum_node,map_sum]; simp only [map_smul, ray_one]; exact Finset.sum_congr rfl fun i _=>real_inner_comm ..
lemma current_eval (A:Dual G)(u:G.Color)(l): inner ℝ u (current A l) = A (key u l) := by
    rw [PiLp.inner_apply,←sum_key,map_sum];simp only [map_smul,current_one];exact Finset.sum_congr rfl fun i _=>real_inner_comm ..

def horizontal (A:Dual G) := ∀ ε:Cover→G.Color,A (gradient ε) = 0
lemma ray_div {A:Dual G} (hp:horizontal A) (x:Cover) : diverge (ray A) x = 0 := by
   ext d
   unfold diverge; simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, ray_one, PiLp.zero_apply]
   let u:=unitColor G d
   let Φ : Cover→G.Color := fun y=> coverLine (y-x) • u
   -- ∑ node difference = gradient Φ
   have he : ∑ i:Axis,(node u (x,i)-node u (x-step i,i))=gradient Φ := by
     funext l; rw [Finset.sum_apply,Finset.sum_eq_single_of_mem l.2 (Finset.mem_univ _)]
     · simp only [node,Pi.sub_apply, gradient, Φ,if_true]; rw [show l.1+step l.2-x=l.1-(x-step l.2) by abel]
     intro i _ h; simp [node,ne_comm.mp h]
   have hh := hp Φ
   rw [← he,map_sum] at hh; simp only [map_sub] at hh; exact hh
lemma row_quake (u:G.Color) (x:Cover) (i:Axis) : (∑ k:Axis,(node u (x+step k,i)+node u (x-step k,i)-2 • node u (x,i))) = -key u (x,i) := by
   funext l
   by_cases hi:l.2=i
   · have hz := laplace (l.1-x)
     rw [Finset.sum_apply]; simp only [node,Pi.sub_apply,Pi.add_apply,key,Pi.neg_apply,hi,↓reduceIte, Pi.smul_apply]
     simp_rw [show ∀ k:Axis,l.1-(x+step k)=l.1-x-step k from fun k=>by abel, show ∀ k:Axis,l.1-(x-step k)=l.1-x+step k from fun k=>by abel, two_smul, ← add_smul, ←sub_smul]
     rw [←Finset.sum_smul, show (∑ i:Axis, (coverLine (l.1-x-step i)+coverLine (l.1-x+step i)-(coverLine (l.1-x)+coverLine (l.1-x)))) = -(if l.1-x=0 then 1 else 0) by rw [←hz]; apply Finset.sum_congr rfl; intro i _; rw [add_comm, two_mul]]
     by_cases he:l.1=x
     · have h : l=(x,i):= Prod.ext he hi
       simp [h]
     simp [sub_ne_zero_of_ne he, show l≠(x,i) from fun h => he (congrArg Prod.fst h)]
   rw [Finset.sum_apply]; simp [node,key,hi,show l≠(x,i) from fun h => hi (congrArg Prod.snd h)]
lemma ray_lap (A:Dual G) (x:Cover) (i:Axis): quake (fun z=> ray A (z,i)) x= -current A (x,i) := by
   ext d; unfold quake; simp only [WithLp.ofLp_sum,Finset.sum_apply,two_smul,PiLp.sub_apply,PiLp.add_apply,PiLp.neg_apply,ray_one,current_one]
   have he := congrArg A (row_quake (unitColor G d) x i)
   simp only [map_sum,two_smul,map_add,map_sub,map_neg] at he;exact he
lemma ray_rest {A:Dual G} (hp:horizontal A) (x:Cover) (i:Axis): starCurl (ray A) x i=current A (x,i) := by rw [radiant,gradient, ray_lap]; simp_rw [ray_div hp]; simp
end YM.RG11Scheme.Stencil
