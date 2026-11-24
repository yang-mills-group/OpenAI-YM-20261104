import YM.QuadraticLocal.Germ.Tariff
/-!
# Complex-letter projection preserving signed estimates (row occupancy with real split)

 Regular multi-stencil envelopes and K use sup over whole complex unit sets, while internal
 comparisons use orientations and **real** response operators. Recover complex-linear label
 certification without re-addressing. Fixed cost ≤ EACH incoming budget (see `.worth` next).
 Uses disjoint marker mode, so multiplicative not a projection on arbitrary densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Affinity.Smalt
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory Push Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[DecidableEq V]{R:Census V}{G:Gauge}{c:Side}
variable {E: V→Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
variable (v:V){F G':(∀ i,E i)→ℂ}
variable (A:∀ i,Set (E i))(K:∀ i, Submodule ℂ (E i))
local notation "Y"=> Full (E:=E)
local notation "Iᴍ"=> Complex.I
def spin (x:Π i,E i) := Function.update x v (Complex.I • x v)
def shadow (v:V)(w:V):ℂ:= if w=v then -Complex.I else 1
def meter (s:Finset V):= ∏ j∈s,shadow v j
variable (R)
def mean (F: (∀ i,E i)→ Poly R) (t:Π i,E i): Poly R:= (2:ℂ)⁻¹ • (F t+ModeWeight.turn R (shadow v) (F (spin v t)))
def solo (F: (∀ i,E i)→ℂ)(s:Finset V)(t: ∀ i,E i):ℂ:= (2:ℂ)⁻¹ * (F t+meter v s*F (spin v t))
variable {R}{s u P:Finset V}{A K}
lemma part (F:(∀ i,E i)→Poly R)(s:R.Mode)(t:Π i,E i): (mean R v F t).part s=solo v (fun t=>(F t).part s) s.val t:= by unfold mean; rw [Poly.part_smul,Poly.part_plus,ModeWeight.scale]; rfl
lemma without (h:v∉s): meter v s=1:=prod_eq_one fun j hj=>if_neg (show j≠v from fun h'=>h (h' ▸ hj))
lemma withMem (h:v∈s): meter v s= -Complex.I:= by unfold meter; rw [prod_eq_single v,shadow,if_pos rfl]; exact fun j _ hj=> if_neg hj; simp [h]
lemma itsNorm : ‖meter v s‖=1:=by
   by_cases h:v∈s; · rw [withMem v h,norm_neg,Complex.norm_I]
   rw [without v h,norm_one]
lemma prevalent (hv:v∉s){Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)]{K:∀ i,Submodule Q (E i)}(h:Eligible K s F):solo v F s = F:= by
   funext t; unfold solo; rw [without _ hv, one_mul,spin,h.full.outside _ hv]; ring
lemma jut (i:V)(hi:i≠v)(t:Π i,E i)(x:E i): spin v (Function.update t i x)=Function.update (spin v t) i x:=by unfold spin; rw [Function.update_of_ne hi.symm, Function.update_comm hi.symm] -- check
lemma twice (t:Π i,E i)(x:E v):spin v (Function.update t v x)=Function.update t v (Complex.I•x):= by unfold spin; rw [Function.update_self,Function.update_idem]
-- linear interpolation on unrestricted tests, at v ∈ budget.
abbrev imported (K: ∀ i,Submodule ℂ (E i)) (i:V) := (K i).restrictScalars ℝ
local notation "Vt"=> imported K
private lemma complexScalar {V:Type*}[AddCommGroup V][Module ℂ V](r:ℝ)(q:ℂ)(x:V): q • (r • x)= r • (q • x):=by rw [← Complex.coe_smul,← Complex.coe_smul,smul_comm]
-- exactly complex-linear slots s' in every s. Others only required real & respect Ann.Claim.
structure Mixed (K:∀ i,Submodule ℂ (E i))(P s:Finset V)(F:(∀ i,E i)→ℂ): Prop where
    honest : Eligible (imported K) s F
    neutral (v:V) : v∈P → v∈s → ∀ (t:Π i,E i)(x:E v), F (Function.update t v (Complex.I•x))= Complex.I * F (Function.update t v x)
lemma honestBlank (h:Eligible (imported K) s F): Mixed K ∅ s F:= ⟨h,fun _ h=> by simp at h⟩
namespace Eligible
lemma faded (h : Affinity.Eligible K s F) : Affinity.Eligible (imported K) s F:= by
   refine ⟨⟨h.full.stay,h.full.join,fun t i hi v a=>?_⟩,h.hollow⟩
   rw [← Complex.coe_smul,← Complex.coe_smul]; exact h.full.scale t i hi ..
lemma mixed (h:Affinity.Eligible K s F) : Mixed K P s F:=⟨faded h,fun v _ hv t x=>h.full.scale t v hv ..⟩
lemma fixed (h:Affinity.Eligible K s F): solo v F s =F:= by
   by_cases hV:v∈s; swap; · exact prevalent v hV h
   funext t; unfold solo; rw [withMem v hV,spin,h.full.scale t v hV Complex.I, smul_eq_mul,Function.update_eq_self,←mul_assoc,neg_mul,Complex.I_mul_I]; ring
lemma sensible {v}
    (h:Affinity.Eligible (imported K) s F)(hp:v∈s) : Affinity.Eligible (imported K) s (F ∘ spin v):=by
   refine ⟨⟨fun t x hX=> h.full.stay _ _ ?_,fun t i hi x y=>?_,fun t i hi r x=>?_⟩,fun i hi t ht=>?_⟩
   · intro i hi; by_cases hx:i=v
     · subst i; rw [spin,spin,Function.update_self,Function.update_self,hX v hp]
     rw [spin,spin,Function.update_of_ne hx,Function.update_of_ne hx,hX _ hi]
   · by_cases hV:i=v
     · subst v; rw [Function.comp_apply,twice, Function.comp_apply,twice, Function.comp_apply,twice,smul_add,h.full.join t i hi]
     rw [Function.comp_apply,jut v _ hV,Function.comp_apply,jut v _ hV,Function.comp_apply,jut v _ hV,h.full.join _ i hi]
   · by_cases hV:i=v
     · subst v; rw [Function.comp_apply,twice,Function.comp_apply,twice,complexScalar,h.full.scale t i hi]
     rw [Function.comp_apply,jut v _ hV,Function.comp_apply,jut v _ hV,h.full.scale _ i hi]
   refine h.hollow i hi _ ?_; by_cases h:i=v; subst v; rw [spin,Function.update_self]; exact Submodule.smul_mem (K i) _ ht
   rw [spin,Function.update_of_ne h]; exact ht
end Eligible
lemma recovered [Fintype V] (h:Mixed K univ s F): Eligible K s F:= by
    let p:=h.honest; refine ⟨⟨p.full.stay,p.full.join,fun t i hi r x=>?_⟩,p.hollow⟩
    have he : r • x = r.re • x+r.im • (Complex.I • x):=by rw [← Complex.coe_smul, ← Complex.coe_smul,smul_smul,← add_smul, Complex.re_add_im]
    rw [he,p.full.join t i hi,p.full.scale t i hi,p.full.scale t i hi,h.neutral i (mem_univ i) hi, ← Complex.coe_smul,← Complex.coe_smul]; simp only [smul_eq_mul]; rw [← mul_assoc, ← add_mul,Complex.re_add_im]
lemma sunrise (h:Mixed K P s F): Mixed K (insert v P) s (solo v F s):=by
   let hp := h.honest; by_cases he:v∈s; swap
   · rw [prevalent _ he hp]; refine ⟨hp,fun i hi hk=>?_⟩; rcases mem_insert.mp hi with rfl|hi; exact False.elim (he hk); exact h.neutral i hi hk
   refine ⟨Affinity.Eligible.cs _ (hp.plus (Affinity.Eligible.cs _ (Eligible.sensible hp he))),fun i hi hI t x=> ?_⟩ -- typo cs
   by_cases hv:i=v
   · subst v; unfold solo; rw [withMem i he,twice,twice,smul_smul,Complex.I_mul_I,neg_smul,one_smul, show -x=(-1:ℝ)•x from (by rw [neg_smul,one_smul]),hp.full.scale t i he,neg_smul,one_smul]; ring_nf; rw [pow_two,Complex.I_mul_I]; ring
   · unfold solo; rw [jut _ i hv,jut _ i hv,h.neutral i ((Finset.mem_insert.mp hi).resolve_left hv) hI t,h.neutral i ((Finset.mem_insert.mp hi).resolve_left hv) hI]; ring

lemma soloZero : solo v (fun t:Y=> 0) s=fun t=>0:=by funext i; simp [solo]
lemma solo_sum {c':Type*}(S:Finset c') (f:c'→ Y →ℂ)(t:Y): solo v (fun t=> ∑ i∈S,f i t) s t=∑ i∈S, solo v (f i) s t:= by simp only [solo,Finset.mul_sum,Finset.sum_add_distrib,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
lemma binds₂ (h:RG3.Held.Letter ℝ E s F)(hh:RG3.Held.Letter ℝ E u G')(hp:Disjoint s u)(t):
    solo v (fun t=>F t*G' t) (s∪u) t= solo v F s t * solo v G' u t:=by
   unfold solo; rw [show meter v (s∪u)=meter v s*meter v u from Finset.prod_union hp]; dsimp only
   by_cases he : v∈s
   · have hv:v∉u:=Finset.disjoint_left.mp hp he
     rw [show G' (spin v t)= _ from hh.outside t hv (Complex.I • t v)]; rw [without v hv]; ring
   rw [show F (spin v t)= _ from h.outside t he (Complex.I • t v)]; rw [without v he]; ring
end YM.QuadraticLocal.Affinity.Smalt
