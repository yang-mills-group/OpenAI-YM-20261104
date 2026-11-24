import YM.MSbar.Counter.Local
import YM.MSbar.Series.Epoch
/-! Static spaces at a chosen ζ, and operations thereon, plus meromorphic rules. Since they are
partial (Laplacian) extend to any symbol families by zero value if outside the domain.
This doesn't remove any pole; everywhere they're used inside recursion we establish
Price/Fits and thus agreement with analytic operations on the common punctured
ε disk. When summing integrated tree identities we work with the subspaces directly. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play
open Dim Symbol Domain Diagram Super Scale Scale.Inertia Function Set Filter Category Counter
open scoped Classical Topology BigOperators
variable {C: Type}{c d e l k : Bit}{W:Edition C}{U:Set ℂ}{i j:ℕ}{V:Finset ℕ}

def stage (W:Edition C)(e:Bit): Submodule ℂ (Vertex C) := {carrier:= {f| Live W e f}, add_mem':= fun h hf=> Live.add h hf, zero_mem':=Live.zero, smul_mem':=fun c _ h=>Live.scale c h}
abbrev Deck (W:Edition C)(e:Bit):= ↥(Play.stage W e)
variable {F G:Functionals C}{f g:Vertex C}{z:ℂ}
-- stage lift
namespace Deck
def plug (W:Edition C)(e:Bit)(f:Vertex C): Deck W e := if h:Live W e f then ⟨f,h⟩ else 0
lemma tall {x:Deck W e} : Live W e x.val:= x.property
@[simp] lemma plug_eq (h:Live W c f): (plug W c f).val=f:=by rw [plug,dif_pos h]
@[simp] lemma plug_val (x: Deck W e): plug W e x.val=x:=by ext1; rw [plug_eq x.property]
@[simp] lemma nil : plug W e 0=0:= Subtype.ext (plug_eq Live.zero)
lemma add' (hf:Live W e f)(hg:Live W e g): plug W e (f+g)=plug W e f+plug W e g:= by ext1; rw [plug_eq (Live.add hf hg)]; rw [Submodule.coe_add,plug_eq hf,plug_eq hg]
lemma scale' (hf:Live W e f)(c:ℂ): plug W e (c•f)= c • plug W e f:=by ext1; rw [plug_eq (Live.scale c hf),Submodule.coe_smul,plug_eq hf]
lemma neg' (hf:Live W e f): plug W e (-f)= -plug W e f:=by ext1; rw [plug_eq (Live.neg hf), Submodule.coe_neg,plug_eq hf]
lemma sub' (hf:Live W e f)(hg:Live W e g): plug W e (f-g)=plug W e f-plug W e g:=by rw [sub_eq_add_neg,sub_eq_add_neg,add' hf (Live.neg hg),neg' hg]
lemma sum' {α:Type*} {I:Finset α} {F:α →Vertex C}(h:∀ i∈I,Live W e (F i)): plug W e (∑ i∈I,F i)=∑ i∈I,plug W e (F i):=by induction I using Finset.induction_on with | empty=> simp | insert i s he ih=> rw [Finset.sum_insert he,Finset.sum_insert he, add' (h i (Finset.mem_insert_self ..)) (Live.sum _ (fun x hx=> h _ (Finset.mem_insert_of_mem hx))), ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj))]
end Deck
open Deck
-- linear motion
abbrev Mono (W:Edition C)(e k:Bit) := ℂ→ Homo (Deck W e) (Deck W k)
abbrev Poly (W:Edition C)(e k l:Bit) := ℂ→ Homo (Deck W e) (Homo (Deck W k) (Deck W l))
def post (A: Mono W e k) (F:Functionals C):Functionals C:=fun z=> (A z (plug W e (F z))).val -- k is nat (!) change e d
lemma post_here {A:Mono W e k}{z:ℂ} : plug W k (Play.post A F z)= A z (plug W e (F z)):= plug_val _
lemma post_live (A:Mono W e k) : Live W k (Play.post A F z):= tall
def twin (A:Poly W e c k)(F G:Functionals C): Functionals C:=fun z=> (A z (plug W e (F z)) (plug W c (G z))).val
lemma twin_here {A:Poly W e c k} : plug W k (twin A F G z)= A z (plug W e (F z)) (plug W c (G z)):= plug_val _
lemma twin_live (A:Poly W e c k): Live W k (twin A F G z):= tall
@[simp] lemma post_0 (A:Mono W e k): Play.post A 0=0:=by funext z; simp [Play.post,nil]
@[simp] lemma twin_zero (A:Poly W e c k): twin A 0 G=0:= by funext z; simp [twin]
@[simp] lemma twin_nil (A:Poly W e c k): twin A G 0=0:= by funext z;simp [twin]
-- Analytic preservation price
abbrev Linear (A:Mono W e k) := ∀ (U:Set ℂ) [Profit U],∀ {F:Functionals C}, Bright U W e F → Bright U W k (Play.post A F)
abbrev Polarized (A:Poly W e c k) := ∀ (U:Set ℂ) [Profit U],∀ {F G:Functionals C}, Bright U W e F → Bright U W c G → Bright U W k (twin A F G)
variable [Profit U]
lemma bound_linear {A: Mono W e k} (h: Linear A)(hf:Price i U W e F): Price i U W k (Play.post A F):= by
    have ⟨G,hG,H⟩:=hf; refine ⟨_,h U hG,fun z hz=>?_⟩; unfold Play.post; rw [swell_inner,← H hz,swell_inner,scale' (hf.alive hz),map_smul]; rfl
lemma bound_poly {A:Poly W e c k}(h:Polarized A)(hf:Price i U W e F)(hg:Price j U W c G): Price (i+j) U W k (twin A F G):= by
    have ⟨X,hX,H⟩:=hf; have ⟨Y,hY,K⟩:=hg; refine ⟨_,h U hX hY,fun z hz=>?_⟩; rw [swell_inner,twin,twin,← H hz,← K hz,swell_inner,swell_inner,scale' (hf.alive hz),scale' (hg.alive hz),map_smul (A z),LinearMap.smul_apply,map_smul,pow_add,← smul_smul]; rfl
end YM.MSbar.Play
