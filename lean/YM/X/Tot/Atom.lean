import YM.X.Tot.Zigg
/-!
# Integral cost ≤1 attachment into unmasked letters, except local mask centers removed by Ward.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed
open Stems hiding X
open Ocean Haze Friend Fielding Print Fund
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable (χ:Floor R)(S: Finset I)(x:I→Fielding.Walk)(z:I→E4)(H:Apart S z r)(hr:R<r)(hx:∀ i∈S,plot q (x i) (z i))(hq:1<q.val)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=> epsilon q
local notation "Ξ"=> Weave q
variable (a b c: Marks G) (A B C:Tops G) {i j k':I}
def shore (q:ℕ+)(χ:Floor R)(S:Finset I)(x:I→Fielding.Walk):Weave q:= 1-∑ i∈S,bend q χ (x i)
lemma quiet_chip (k:ℕ)(v:Site (side q k)): shore q χ S x k v=↑(Porch.Quiet q S x χ k v):= by unfold shore Porch.Quiet bend; simp [Finset.sum_apply]
include hq H hr hx
lemma seashore (X:Weave q)(h:Isle q S x z χ 6 (fun t=> X t.1 (wrap _ t.2))) : Released (crow q (shore q χ S x * X)):= by
   have he:= expand_suite hq S x z hx χ (fun i hi j hj he=> hr.trans (H i hi j hj he)) h; apply Eq.mp ?_ he; congr 1; ext1 k; simp_rw [wrap_lift,crow,Pi.mul_apply,quiet_chip,Complex.real_smul,volS,Complex.ofReal_pow]
lemma mote (hi:i∈S)(hj:j∈S)(hk:k'∈S):
    let t:=wire q (x i) a A * wire q (x j) b B * wire q (x k') c C; Released (crow q (shore q χ S x*t)):= by
     intro t; apply seashore χ S x z H hr hx hq; have h(t:Marks G)(v:Tops G)(i:I)(hi:i∈S): Isle q S x z χ 2 (fun z=> wire q (x i) t v z.1 (wrap _ z.2)):= wire_far χ v t hq S x z (fun s hi t hj h=> hr.trans (H s hi t hj h)) hx hi
     exact ((h a A i hi).mul (h b B j hj)).mul (h c C k' hk)
def atMost (x i j k:I):Prop:= ((x=i→x≠j∧x≠k)∧(x=j→x≠k))
lemma most (hi:i∈S)(hj:j∈S)(hk:k'∈S)(T:Finset I)(h:T⊆S)(hp:∀ d∈S\T,atMost d i j k'):
    let t:=wire q (x i) a A * wire q (x j) b B * wire q (x k') c C; Released (crow q (shore q χ T x*t)):= by
     intro t; have he:T∪ (S\T)=S:= by rw [Finset.union_sdiff_of_subset h]; -- edit
     have h₁: shore q χ T x= shore q χ S x+∑ i∈S\T,bend q χ (x i):= by
        unfold shore; nth_rw 1 [← he]; rw [Finset.sum_union Finset.disjoint_sdiff]; ring
     rw [h₁,add_mul, Finset.sum_mul, crowd_plus,crowd_onto]; apply Released.add (mote χ S x z H hr hx hq a b c A B C hi hj hk);
     let P:= wire q (x i) a A; let Q:=wire q (x j) b B; let Z:= wire q (x k') c C; let f(d:I):=crow q (bend q χ (x d)*t); refine (show Released _ from ?_); change (∑ i∈S\T,f i) ∈ Shelf.crew; apply Submodule.sum_mem; intro d hd; have hs:= Finset.mem_sdiff.mp hd|>.1; let w:= bend q χ (x d); let R' (s:Weave q):= Chase q r 0 (fromX q (x d) s); have he (t:Marks G)(v:Tops G)(i:I)(hi:i∈S)(hy:d≠ i): R' (wire q (x i) t v):= wire_step _ _ _ _ hq (hx i hi) (x d) (hx d hs) (χ.positive.trans hr).le (H _ hi d hs (Ne.symm hy));
     let hpp:= hp d hd; change Released (crow q (w*(P*Q*Z))); by_cases ht:d=i
     · subst d; exact single_glint χ _ hq _ _ _ hr (single_seed _ _ _) (he _ _ _ hj (hpp.1 rfl|>.1)) (he _ _ _ hk (hpp.1 rfl|>.2))
     have hu:= he a A i hi ht; by_cases ht':d=j; · rw [mul_comm P Q]; subst d; exact single_glint χ _ hq _ _ _ hr (single_seed _ _ _) hu (he _ _ _ hk (hpp.2 rfl))
     have hw:=he b B j hj ht'; by_cases hu':d=k'; · rw [mul_comm (P*Q),← mul_assoc Z P Q]; subst d; exact single_glint χ _ hq _ _ _ hr (single_seed _ _ _) hu hw
     apply no_glint χ (x d) hq (P*Q*Z) hr; rw [from_mul,from_mul]; exact Chase.mulC hq (hu.mulC hq hw) (he _ _ _ hk hu') -- apply hu elaborates
end YM.PositionX.Tot
