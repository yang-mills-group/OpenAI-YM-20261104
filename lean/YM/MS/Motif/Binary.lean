import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.BilinearMap
import YM.MS.Heat.Silo
import YM.MS.Plane

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset Metric Real
open Plane Koszul Heat Flux
open scoped Topology
variable {A P R B:Type} [CommRing R] [AddCommGroup P] {p:Sector A} {b c:Bool} {u f g:Row A P R} {i:A}
local infixl:67 "⋄"=> product (field p)
def tip (p:Sector A)(i:A)(u g:Row A P R)(v: Legs (Mode A P)): R:= scatter (field p) v (fun l t=>u l*g ((i,net l)::t))
lemma sp0 (J:Finset B){f:B→ Shared A R}(l:Legs A): scatter p l (fun i j=>∑ x∈J,f x i j)=∑ x∈J, scatter p l (f x) := by rw [show (fun i j=>∑ x∈J,f x i j)=_ from (show _=∑ x∈J,f x from funext fun i=> funext fun j=> by simp only [Finset.sum_apply])]; exact map_sum (allocate p l) .. -- may fail
def quash (p:Sector A)(i:A): Row A P R→ₗ[R] Row A P R→ₗ[R] Row A P R:= LinearMap.mk₂ R (tip p i) (fun F H W=>funext fun l=> show tip p i ( F+H) W l=_ from (calc
       _= allocate _ l ((fun a b=>F a*W ((i,net a)::b))+(fun a b=>H a*W ((i,net a)::b))):=by apply scatter_congr; intro a b _; simp [add_mul]
       _=_:= map_add ..)) (fun c F H=>funext fun l=>by
          change allocate (field p) l (fun x y=>(c•F) x* H ((i,net x)::y))=_; rw [show (fun (x y:Legs (Mode A P))=>(c•F) x*_)=_ from (show (fun (x y:Legs (Mode A P))=>(c•F) x* H ((i,net x)::y))= c • (fun x y=>F x*H ((i,net x)::y)) from by ext; simp [mul_assoc])]; exact map_smul ..) (fun f g h=>funext fun l=> show tip p i f (g+h) l=_ from (calc
             _= allocate _ l ((fun a b=>f a*g ((i,net a)::b))+(fun a b=>f a*h ((i,net a)::b))):= by apply scatter_congr; intro a b _; simp [mul_add]
             _=_:= map_add ..)) (fun c f g=>funext fun l=>by
               change allocate (field p) l _ = c • tip p i f g l; unfold tip; change allocate (field p) l (fun x y=>f x* (c•g) ((i,net x)::y))= c • allocate (field p) l _; rw [← map_smul]; congr 1; ext; simp [mul_left_comm])
lemma quamped (i:A)(u g:Row A P R): quash p i u g= tip p i u g:= rfl
open Classical in
def stint (u:Row A P R)(x:P) : Row A P R:= fun l=> if net l=x then u l else 0
lemma stint_tone (h:Pure (field p) b u)(x:P): Pure (field p) b (stint u x):=fun l hl=> by simp only [ stint,h l hl,ite_self]
lemma recover (i:A)(u g:Row A P R)(l:Legs (Mode A P)): ∀ᶠ t:Finset P in atTop,(quash p i u g) l=(∑ j∈ t,(stint u j)⋄ D (i,j) g) l:= by
   classical
   unfold quash tip; simp only [LinearMap.mk₂_apply, Finset.sum_apply,scattered]; simp_rw [← sp0]; apply EventuallyEq.symm; refine gathers _ _ _ _ (fun x y h=>?_); filter_upwards [eventually_ge_atTop ({net x}:Finset P)] with t ht; let z:=net x; rw [Finset.sum_eq_single_of_mem z (ht (Finset.mem_singleton_self _))]; exact (by simp [stint,z]); intro j hj he; simp [stint,show net x≠j from he.symm]
omit [AddCommGroup P] in
lemma prod_event {X: Type}{u v: Row A P R}{L:Filter X}{F H:X→ Row A P R}(h:∀ i,∀ᶠ x in L,F x i=u i)(hp:∀ i,∀ᶠ x in L,H x i=v i)(w:Legs (Mode A P)): ∀ᶠ x in L,(F x⋄H x) w=(u⋄v) w:= by simp_rw [scattered]; refine gathers _ _ _ _ (fun x y _=>?_); filter_upwards [h x,hp y] with t h1 h2; rw [h1,h2]
lemma q_prod {i:A}(hu:Pure (field p) (b.xor (p i)) u)(hf:Pure (field p) c f) : quash p i u (f⋄g) = (quash p i u f) ⋄ g +(cross b c:R) • ( f ⋄ (quash p i u g)) := by
   funext l; let h (S: Finset P)(f:Row A P R):=(∑ x∈S, stint u x ⋄ D (i,x) f); have he (F: Row A P R)(l:Legs (Mode A P)): ∀ᶠ w:Finset P in atTop, h w F l=quash p i u F l:= EventuallyEq.symm (recover i u F l)
   have hy (S:Finset P): h S ( f⋄g)= h S f ⋄ g+(cross b c:R) • (f ⋄ h S g) := by
       unfold h; simp_rw [ map_sum,LinearMap.sum_apply,D_product, map_add, field,hf.signs,map_smul,LinearMap.smul_apply,Finset.smul_sum,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j hj=>?_ ; simp_rw [← times_assoc]; congr 1; rw [map_smul,← times_assoc (stint u j), (stint_tone hu j).times_comm hf,map_smul,LinearMap.smul_apply]; simp only [smul_smul]; congr 1; cases hi:p i <;> cases b <;> cases c <;> simp
   obtain ⟨s,h₁,h₂,h₃⟩:= (( he (f⋄g) l).and ((prod_event ( fun l=>he f l) (fun i=>Eventually.of_forall fun _=> (rfl:g i=g i)) (p:=p) l).and (prod_event (p:=p) (fun i=>Eventually.of_forall fun _:Finset P=> (rfl:f i=f i)) (he g) l))).exists
   rw [← h₁,hy,Pi.add_apply,Pi.smul_apply,h₂,h₃]; rfl
end YM.MS.Motif
