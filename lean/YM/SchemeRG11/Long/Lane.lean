import YM.SchemeRG11.Long.Plain
/-! Basis of translating stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open scoped Classical
variable {G:Gauge} {R:ℝ} {I:Type*}
def flex (z:Cover): Touch G→ₗ[ℝ]Touch G:= Finsupp.lmapDomain ℝ ℝ (Acorn.rise z)
abbrev idi(p:Shaft G):Touch G:=Finsupp.single p 1
lemma flex_one (z:Cover)(p:Shaft G):flex z (idi p)=idi (rise z p):=by simp [flex,idi]
def tuck (p:Shaft G→ℝ)(z:Cover)(u:Shaft G) := p (rise z u)
lemma flex_eval(x:Shaft G→ℝ)(z:Cover)(v:Touch G):sense x (flex z v)=sense (tuck x z) v:=by
 induction v using Finsupp.induction_linear with
 | zero=>simp
 | add a b ha hb=>simp only [map_add,ha,hb]
 | single i b=>simp [flex,sense,tuck]
lemma grain (p:Shaft G→ℝ)(v:Shaft G): sense p (idi v)=p v:=by simp [sense,idi]
lemma strain {v w:Touch G}(h:∀p:Shaft G→ℝ,sense p v=sense p w):v=w:=by
 ext k; let C:= (Finsupp.lapply (R:=ℝ) (M:=ℝ) k:Touch G→ₗ[ℝ] ℝ)
 let p : Shaft G→ℝ:= Pi.single k 1
 have H:C=sense p:=by ext i;simp only [C,sense,p]; by_cases he:i=k<;>simp [he,Ne.symm]
 change C v=C w;rw [H,h]
-- exact plain translating pair
lemma rise_form (p:Shaft G)(x y:Cover):rise x (rise y p)=rise (x+y) p:=by cases p; unfold rise; dsimp; congr 2; abel
lemma flex_mul (v:Touch G)(x y:Cover):flex x (flex y v)=flex (x+y) v:=by apply strain; intro p; simp only [flex_eval]; unfold tuck; simp only [rise_form]
lemma flex_zero (v:Touch G): flex 0 v=v:=by apply strain; intro p; rw [flex_eval,show tuck p 0=p from funext fun i=>by simp [tuck,rise]]
-- construct flex differences via commutive
variable (G)
def rift(i:Axis):Module.End ℝ (Touch G):=flex (step i)-1
lemma rifts(i j:Axis):Commute (rift G i) (rift G j):=by
 apply LinearMap.ext; intro v; change (flex _ (flex _ v-v)-(flex _ v-v))=(flex _ (flex _ v-v)-(flex _ v-v))
 rw [map_sub,map_sub,flex_mul,flex_mul,add_comm (step i)]; abel
variable {G}
def riffle (v:Fliers):Module.End ℝ (Touch G):=(v.map (rift G)).noncommProd (fun i (h:_∈_) j (k:_∈_) _=>by obtain ⟨a,_,rfl⟩:= Multiset.mem_map.mp h; obtain ⟨b,_,rfl⟩:= Multiset.mem_map.mp k; exact rifts ..)
lemma riffle_cons (i:Axis)(t:Fliers): riffle (i ::ₘ t)=rift G i*riffle t:=by simp only [riffle,Multiset.map_cons,Multiset.noncommProd_cons]
lemma fade (v:Fliers)(p:Touch G)(x:Shaft G→ℝ)(z:Cover): sense x (flex z (riffle v p))= fleet v (fun t=>sense x (flex t p)) z:=by
 induction v using Multiset.induction generalizing z with
 | empty=>rfl
 | cons i s ih=>rw [riffle_cons,fleet_cons]; rw [show (rift G i * riffle s : Module.End ℝ (Touch G)) p=flex (step i) (riffle s p)-riffle s p from rfl,map_sub,map_sub,flex_mul,ih,ih]; exact Eq.symm (soar_apply i _ z)
abbrev vane0(p:Shaft G)(s:Fliers):Touch G:=riffle s (idi p)
def element (p:Shaft G→ℝ)(i:Axis)(c:G.ColorIndex)(x:Cover):=p ((x,i),c)
lemma dip(p:Shaft G→ℝ)(i:Shaft G)(s:Fliers)(a:Cover):sense p (flex a (vane0 i s))=fleet s (element p i.1.2 i.2) (a+i.1.1):=by
 rw [vane0,fade]; conv_lhs=> simp only [flex_one,grain]
 rw [←jump s (element p i.1.2 i.2)]; rw [show (fun t=> p (rise t i))=hop i.1.1 (element p i.1.2 i.2) by funext t; dsimp only [hop,LinearMap.coe_mk,AddHom.coe_mk, element,rise]; rw [add_comm]]
def Stepper(G:Gauge)(m:ℕ):Submodule ℝ (Touch G):= Submodule.span ℝ {u|∃ i:Shaft G,∃s:Fliers,s.card=m∧u=vane0 i s}
lemma rider (i:Shaft G)(s:Fliers):vane0 i s∈Stepper G s.card:=Submodule.subset_span ⟨i,s,rfl,rfl⟩
lemma ride {i:Shaft G}{s:Fliers}{m:ℕ}(h:s.card=m):vane0 i s∈Stepper G m:=h ▸ rider i s
lemma blank_step (u:Touch G): u∈Stepper G 0:=by
 induction u using Finsupp.induction_linear with
 | zero=> exact Submodule.zero_mem _
 | add i j hi hj=> exact Submodule.add_mem _ hi hj
 | single i b=> rw [show Finsupp.single i b=b • vane0 i 0 by change _= b • Finsupp.single i (1:ℝ);simp]; exact Submodule.smul_mem _ _ (ride rfl)
lemma high_i(i j:Axis)(x:Cover)(g:G.ColorIndex): intake x i j g∈Stepper G 1:=by
 let s:Fliers:=i ::ₘ 0; let t:Fliers:=j ::ₘ 0
 let a:Shaft G:=((x,j),g); let b:Shaft G:=((x,i),g)
 rw [show intake x i j g=vane0 a s-vane0 b t from ?_]; exact Submodule.sub_mem _ (ride (by simp [s])) (ride (by simp [t]))
 apply strain; intro p; rw [map_sub, ←flex_zero (vane0 a s), ←flex_zero (vane0 b t),dip,dip]
 rw [← Tree.cant_inv p,speak]; let U:=linkup.symm (tint p); rw [show tint p=linkup U from rfl,North.intake_g]; dsimp only [s,t]; rw [fleet_cons,fleet_cons,zero_add];rfl
end YM.SchemeRG11.Long
