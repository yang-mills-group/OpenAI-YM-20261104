import YM.X.Braid.Stitch
/-!
# Recursions with all spatial markers. On warmed variables
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Asymptotics Reed Braid Finset
open scoped Topology ContDiff BigOperators
variable {V I: Type*}
local notation "𝒫"=> Normal.poly V
variable (Q:Symmetric V)(f:I → poly V)(p q p': poly V) [DecidableEq I] (s:Finset I) (L:V→₀ℂ)
-- all polys are in one n-periodic unlifted alphabet. finite energy.
def spiro (p:𝒫):= milk Q (milk (-Q) p * ∏ i∈s,milk (-Q) (f i))
abbrev spine (p:𝒫) := (aeval (0:V→ℂ)) (spiro Q f s p) -- no self-eye.
variable {Q}
namespace spiro
@[simp] lemma nil : spiro Q f ∅ p=p:=by simp [spiro,miles]
lemma surge {g:I→𝒫}(h:∀ i∈s,f i=g i): spiro Q f s p=spiro Q g s p:= by unfold spiro; rw [Finset.prod_congr rfl (show ∀ i∈s,milk (-Q) (f i)=milk (-Q) (g i) from fun i hi=>congr_arg _ (h i hi))]
lemma insertNew {i:I}(h:i∉ s): spiro Q f (insert i s) p=knot Q (f i) (spiro Q f s p):= by unfold spiro knot; rw [minus,prod_insert h];apply congr_arg (milk Q); ring
lemma slip_arrive (i:I)(hi:i∉s) : spiro Q (Function.update f i q) s p=spiro Q f s p := surge (Function.update f i q) p s (fun _ hz=> Function.update_of_ne (ne_of_mem_of_not_mem hz hi) ..)
lemma pulse {i:I}(hi:i∈s): spiro Q (Function.update f i q) s p= knot Q q (spiro Q f (s.erase i) p):= by
    nth_rw 1 [← Finset.insert_erase hi]; rw [insertNew _ _ _ (Finset.notMem_erase _ _),Function.update_self,slip_arrive _ _ _ _ _ (Finset.notMem_erase _ _)]
-- simplify via shifting updates
lemma pulse₁ {i:I}(hi:i∈s): spiro Q f s p=knot Q (f i) (spiro Q f (s.erase i) p):= by
   nth_rw 1 [← Finset.insert_erase hi]; rw [insertNew _ _ _ (Finset.notMem_erase _ _)]
lemma xadd : spiro Q f s (p+q)=spiro Q f s p+ spiro Q f s q:= by unfold spiro; rw [map_add,add_mul,map_add]
lemma xscale (a:ℂ): spiro Q f s (a • p)=a • spiro Q f s p:=by unfold spiro;rw [map_smul,smul_mul_assoc,map_smul]
def slot (Q:Symmetric V)(i:I) (hi:i∈s): 𝒫→ₗ[ℂ] 𝒫:= (oral Q).flip (spiro Q f (s.erase i) p)
lemma slot_point {i:I}(hi:i∈s): slot f p s Q i hi q=spiro Q (Function.update f i q) s p:= by rw [pulse f p q s hi]; rfl -- order check
lemma add_at {i:I}(hi:i∈s)(g x:𝒫):spiro Q (Function.update f i (g+x)) s p=spiro Q (Function.update f i g) s p + spiro Q (Function.update f i x) s p:=by simp_rw [← slot_point f p _ s hi,map_add]
lemma scale_at {i:I}(hi:i∈s)(a:ℂ): spiro Q (Function.update f i (a • q)) s p=a • spiro Q (Function.update f i q) s p:= by rw [pulse _ _ _ s hi,pulse _ _ _ s hi, pscale]
lemma sum_at {i:I}(hi:i∈ s){J:Type*}(g:J→𝒫)(l:Finset J): spiro Q (Function.update f i (∑ t∈l,g t)) s p= ∑ t∈l,spiro Q (Function.update f i (g t)) s p:= by simp_rw [← slot_point f p _ s hi,map_sum]
lemma amend {i:I}(hi:i∈s): spiro Q (Function.update f i q) s p=spiro Q f (s.erase i) (knot Q p q):= by rw [pulse _ _ _ s hi, spiro,spiro,knot,knot,minus,minus]; apply congr_arg (milk Q); ring
-- derivative through product Formula
lemma spiralD : edge Q L (spiro Q f s p)= spiro Q f s (edge Q L p) + ∑ i∈s, spiro Q (Function.update f i (edge Q L (f i))) s p:= by
    induction s using Finset.induction_on with
    | empty=>simp
    | insert i s hi IH=>
       have he(i:I)(x:I→𝒫)(b:𝒫){s:Finset I}(hi:i∉s): spiro Q x (insert i s) b= _ := insertNew x b s hi -- infer?
       rw [he i _ _ hi, show edge Q L (knot Q (f i) (spiro Q f s p))= knot Q (edge Q L (f i)) (spiro Q f s p) + knot Q (f i) (edge Q L (spiro Q f s p)) from skimmers .., IH]
       simp_rw [sum_insert hi,he i _ _ hi,Function.update_self]; rw [slip_arrive f p _ s i hi]
       have hx :∑ j∈s, knot Q (Function.update f j (edge Q L (f j)) i) (spiro Q (Function.update f j (edge Q L (f j))) s p)= knot Q (f i) (∑ j∈s,spiro Q (Function.update f j (edge Q L (f j))) s p):= by
           rw [pcomm Q (f i),Braid.psum]; apply Finset.sum_congr rfl; intro b hb; rw [Function.update_of_ne (ne_of_mem_of_not_mem hb hi).symm, pcomm];
       rw [padd',hx]; abel
end spiro
end YM.PositionX.Crate
