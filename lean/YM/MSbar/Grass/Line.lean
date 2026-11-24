import YM.MSbar.Grass.Intertwine

/-! Linearity in stock. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset Finsupp
open scoped BigOperators Classical
variable {T:Type*} {p:T→Bit} {f g : Series T}{x y:T} {d e r k : Bit} {P D : Stock T}

def treeing (p:T→Bit)(d:Bit): Stock T →ₗ[ℂ] Double T:= Finsupp.linearCombination ℂ (fun x=> (2:ℂ)⁻¹ • member p d x)
lemma trest (P : Stock T): pairs p d P=treeing p d P:=by
    unfold pairs treeing Finsupp.linearCombination; dsimp [Finsupp.sum]; simp_rw [smul_smul]; simp only [div_eq_mul_inv]
lemma pairs_sum {ι:Type*} (p:T→Bit)(d:Bit)(X:Finset ι)(F:ι→Stock T): pairs p d (∑ i∈X,F i)=∑ i∈X,pairs p d (F i):=by simp_rw [trest];exact map_sum ..
lemma pairs_single (a:T × T)(c:ℂ): pairs p d (Finsupp.single a c) f g=(c/2) • member p d a f g:=by rw [trest]; unfold treeing; rw [Finsupp.linearCombination_single]; simp [div_eq_mul_inv,smul_smul]
lemma pair_add : pairs p d (P+D)=pairs p d P + pairs p d D:= by simp_rw [trest,map_add]
lemma pair_smul (c:ℂ): pairs p d (c • P)= c • pairs p d P:= by simp_rw [trest,map_smul]

lemma Grade.reveal : Grade p d P ↔ ∀ x:T×T,p x.1+p x.2≠d → P x=0 := by
    constructor <;> intro h x hv <;> contrapose! hv
    · exact h _ (Finsupp.mem_support_iff.mpr hv)
    exact fun hz=> (Finsupp.mem_support_iff.mp hz) (h _ hv)
lemma Grade.single {v:ℂ} (hp:v=0∨p x+p y=d) : Grade p d (Finsupp.single (x,y) v):=by
    apply reveal.mpr; intro a h; by_cases ht:(x,y)=a <;> cases hp with
    | inl h=> simp [h]
    | inr he=> first | { simp [Finsupp.single_apply,ht]; done } | { subst a; exact (h he).elim }
lemma Grade.sum {ι:Type*}{F:ι→Stock T} {I:Finset ι}(he:∀ i∈I,Grade p d (F i)) : Grade p d (∑ i∈I,F i):=by
    refine Grade.reveal.mpr fun x hx=> ?_; rw [Finsupp.finsetSum_apply];exact Finset.sum_eq_zero fun i hi=> Grade.reveal.mp (he i hi) x hx
lemma Grade.minus (hp:Grade p d P): Grade p d (-P):= reveal.mpr (fun x hx=> by rw [Finsupp.neg_apply,reveal.mp hp x hx,neg_zero])
end YM.MSbar.Super
