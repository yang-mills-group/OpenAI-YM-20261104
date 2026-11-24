import YM.FVA2.BlockWedge

/-!
# Paired Wick computation of the Faddeev-Popov density factor

`generator_integral` does not construct a measure on odd spaces. Use the list
calculus of `Endμ`, at all g-orders, with ranks checked before each occurrence.
It handles an optional additional even weight (full marked integrands) with no
antighost letters. Entries of the determinant are **series over the retained
boson fields**, not evaluated independently in the vacuum Wick measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Paper
open Filter
open MS MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater Finset PowerSeries PairCoords
open scoped Topology Classical ContDiff
variable {U J:Type}
local notation "ψ"=>φ (U:=U) (J:=J)
local notation "q"=>Price ψ
local notation "B"=>rowPair (U:=U)

def Omits {A:Type} {p:Sector A} (j:A)(f:Price p): Prop:=∀ i,D j (track p f i)=0
variable {A:Type}{p:Sector A} (j i:A) {f g:Price p}
lemma omit_add (h:Omits j f)(hp:Omits j g): Omits j (f+g) := by intro i; rw [map_add,Pi.add_apply,map_add,h i,hp i,add_zero]
lemma omit_zero : Omits j (0:Price p) := by intro i; rw [map_zero,Pi.zero_apply,map_zero]
lemma omit_one : Omits j (1:Price p) := by intro i; rw [tracking,coeff_one]; split; exact coin_nod j (1:ℂ); exact map_zero _
lemma omit_const (F: Dark p)(h: D j F.val=0): Omits j (C F) := by intro i; rw [tracking,coeff_C]; split; exact h; exact map_zero _
lemma omit_prod (h:Omits j f)(hp:Omits j g): Omits j (f*g):= by
   intro i; rw [pair]; change D j (∑ x∈antidiagonal i, product p (track p f x.1) (track p g x.2)) = _; rw [map_sum]; apply Finset.sum_eq_zero; intro x _; rw [D_product,h x.1,hp x.2,map_zero, map_zero,LinearMap.zero_apply, add_zero]
lemma omit_many {W:Type*} (S:Finset W)(f:W→Price p)(h:∀ i∈S,Omits j (f i)): Omits j (∏ i∈S,f i):= by induction S using Finset.induction_on with | empty=> rw [Finset.prod_empty]; exact omit_one _| insert i s hi ih=> rw [Finset.prod_insert hi]; exact omit_prod _ (h _ (by simp)) (ih fun j hj=> h _ (by simp [hj]))
lemma omit_sum {B':Type*}(S:Finset B')(f:B'→Price p)(h:∀ i∈S,Omits j (f i)): Omits j (∑ i∈S,f i):= by induction S using Finset.induction_on with| empty=>rw [Finset.sum_empty]; exact omit_zero _| insert i s hi ih=>rw [Finset.sum_insert hi]; exact omit_add _ (h _ (by simp)) (ih fun _ hu=> h _ (Finset.mem_insert_of_mem hu))
lemma omit_sub (h:Omits j f)(hp:Omits j g): Omits j (f-g):= by intro i; rw [map_sub,Pi.sub_apply,map_sub,h i,hp i,sub_self]
lemma omit_smul (h:Omits j f)(c:ℂ) : Omits j (c • f):= by intro i; rw [map_smul,Pi.smul_apply, map_smul, h i,smul_zero]
lemma omit_exp (h:Omits j f): Omits j (exp f):= by
   intro i; rw [tracking, Paper.exp,coeff_mk,← tracking]; apply omit_sum
   intro j' _; apply omit_smul; induction j' with| zero=>rw [pow_zero]; exact omit_one _| succ n ih=>rw [pow_succ]; exact omit_prod _ (ih (Finset.mem_range.mpr (by rename_i H; obtain he:= Finset.mem_range.mp H; omega))) h

variable {x y : Price (φ (U:=U) (J:=J))}

section
local infixl:70 " ● "=> product ψ
abbrev ForBar (i:J) (x:q) := Omits (bar i) x
lemma shut_row (j i k:J)(h:j≠i): ForBar i (B j k):= by
   apply omit_const; change D _ (_ ● _)=0; rw [D_product, unheard (PairCoords.c k) (show bar i≠PairCoords.c (U:=U) k from (by simp [bar,PairCoords.c])), unheard (bar j) (show bar i≠bar j from (by simpa [bar] using (Ne.symm h))),map_zero,map_zero]; simp -- linear
lemma costs_row (i j:J) : Bound (B i j):= bound_C _ (fee_pair (p:=ψ) (f:=atLetter (PairCoords.c j)) (h:=atLetter (bar i)) ⟨speaks_s _,minH (letterN _)⟩ ⟨speaks_s _,minH (letterN _)⟩)
variable [Fintype U][Fintype J](Y:Grain U)(h:∀ a b:U,Y a b=Y b a) -- fix
include h
lemma replaceV (p:J) {F':BL (Slot U J)} (he: D (bar p) F'=0) (hp:F'∈FeeP ψ): View (major Y) (PairCoords.block U p p ● F') = View (major Y) F':= by
   rcases fee_spec hp with ⟨hp,hv⟩; rw [PairCoords.block,times_assoc,_root_.YM.MS.Swirl.ibpV (F:=(atLetter (bar p)) ● F') (PairCoords.c p) (order Y) (rule Y h) ((speaks_s (bar (U:=U) p)).times hp) (miPair (minH (letterN _)) hv),Finset.sum_eq_single (bar p)]; rotate_left
   · intro j hj hh; rw [cost_c, if_neg hh,zero_mul]
   · simp
   rw [cost_c,if_pos rfl,one_mul, D_product,hear,coin_product,one_smul,he,map_zero,add_zero]
lemma supplant (i:J) (hc:ForBar i x)(hx:Bound x): ℶV (major (J:=J) Y) (track ψ (B i i*x))=ℶV (major (J:=J) Y) (track ψ x):= by
   ext1 r; change View _ (track ψ _ r)= _; unfold rowPair; rw [trackC_mul]; exact replaceV Y h i (hc r) (hx r (Set.mem_univ r))
private lemma finale (F:Finset J) (hx:Bound x)(hB:∀ j∈F, ForBar j x): ℶV (major (J:=J) Y) (track ψ ( (∏ i∈F,B i i )*x ))= ℶV (major (J:=J) Y) (track ψ x):= by
   induction F using Finset.induction_on with| empty=>rw [Finset.prod_empty,one_mul]| insert a s he ih=> rw [Finset.prod_insert he,mul_assoc,supplant Y h a (omit_prod _ ?_ (hB a (by simp))) (bound_pair ?_ hx), ih (fun _ hy=> hB _ (Finset.mem_insert_of_mem hy))]; exact omit_many _ _ _ fun j hj=> shut_row _ _ _ (fun h=> he (h ▸ hj)); exact bound_prod _ _ fun j _=> costs_row j j

variable (fW:J→Price (φ (U:=U) (J:=J)))(Hf:∀ i,Bound (fW i))(hg:∀ i j,i≠j→ForBar j (fW i))
include Hf hg
lemma augment (F:Finset J) (hx:Bound x)(hB:∀ j∈F, ForBar j x) : ℶV (major (J:=J) Y) (track ψ ( (∏ i∈F,(1+fW i) )*x ))= ℶV (major (J:=J) Y) (track ψ ( (∏ i∈F,(B i i+fW i))*x)) := by
   induction F using Finset.induction_on generalizing x with
   | empty=> simp
   | insert a s he ih=>
      have ht: ∀ i∈s, ForBar i x:=fun i hi=> hB _ (Finset.mem_insert_of_mem hi)
      let V:=∏ i∈s,(1+fW i); let T:=∏ i∈s,(B i i+fW i)
      rw [Finset.prod_insert he, Finset.prod_insert he,mul_assoc (1+fW a), mul_assoc (B a a + fW a), add_mul, add_mul,one_mul,map_add,map_add,map_add,map_add]
      apply congr_arg₂ (·+·)
      · symm; rw [supplant Y h a (omit_prod _ ?_ (hB a (by simp))) (bound_pair ?_ hx)]; exact (ih hx ht).symm
        · exact omit_many _ s _ fun i hi=> omit_add _ (shut_row i a i (fun h=> he (h ▸ hi))) (hg _ _ (fun h=> he (h ▸ hi)))
        exact bound_prod s _ fun i _=> bound_add (costs_row i i) (Hf i)
      change ℶV (major (J:=J) Y) (track ψ (fW a * (V*x)))=ℶV (major (J:=J) Y) (track ψ (fW a * (T*x)))
      rw [mul_left_comm (fW a) V, mul_left_comm (fW a) T]; exact ih (bound_pair (Hf a) hx) (fun i hi=> omit_prod _ (hg _ _ (fun h=> by rw [h] at he; contradiction)) (ht _ hi))

omit Hf hg
variable [DecidableEq J] (V:Matrix J J (Price (φ (U:=U) (J:=J))))
   (HV:∀ i j, Bound (V i j))
   (hv:∀ i j k, ForBar i (V j k))
local notation "ζW"=> ℶV (major (J:=J) Y)
-- χ only the positive-order generator. Spell M=1+V later.

def patches (U:Type) (V:Matrix J J (Price (φ (U:=U) (J:=J)))) : Price (φ (U:=U) (J:=J)) := ∑ i:J, turnP i U (V i)
omit h [Fintype U] [DecidableEq J] in
lemma patch0 (i:J)(hB0:∀ i j,coeff 0 (V i j)=0): coeff 0 (turnP i U (V i))=0:= by unfold turnP; simp [ - coeff_zero_eq_constantCoeff,hB0, coeff_mul ] -- avoid simp recursion
omit h [Fintype U] [DecidableEq J] in
lemma produces (hB0:∀ i j,coeff 0 (V i j)=0): exp (patches U V)=∏ i:J,(1+turnP i U (V i)):= by
   let f i:=turnP i U (V i); have hz i:coeff 0 (f i)=0:= patch0 V i hB0; suffices ht:∀ s:Finset J, exp (∑ i∈s,f i)=∏ i∈s,(1+f i) by exact ht _
   intro s; induction s using Finset.induction_on with| empty=> simp| insert i s he ih=> rw [Finset.sum_insert he,Finset.prod_insert he, exp_add _ _ (hz _) (by rw [map_sum]; exact Finset.sum_eq_zero fun _ _=> hz _), ih, exp_sink _ (hz _) (turn_same _ _ _)]
-- burdens on functions.Scalar torsion
variable {a: ℤ}
omit h [Fintype U] [Fintype J] [DecidableEq J] in
lemma bound_sign (a:ℤ)(w:q)(H:Bound w) : Bound (a • w) := by intro i _; rw [map_zsmul,Pi.smul_apply]; exact (FeeP ψ).toAddSubgroup.zsmul_mem (H i (Set.mem_univ i)) a
omit h [Fintype U] [Fintype J] [DecidableEq J] in
lemma shut_sign (i:J)(a:ℤ)(w:q)(H:ForBar i w): ForBar i (a • w):= by intro j; rw [map_zsmul,Pi.smul_apply,map_zsmul,H j,smul_zero]

include h HV hv
theorem generator_integral (hx:Bound x)(ht:∀ i, ForBar i x)(hB0:∀ i j,coeff 0 (V i j)=0):
   ℶV (major (J:=J) Y) (track ψ (exp (patches U V)*x)) = ℶV (major (J:=J) Y) (track ψ ((1+V).det*x)) := by
   let f i:=turnP i U (V i); have ht' (i:J): B i i+turnP i U (V i)=turnP i U ((1+V) i):= by
      have he : rowPair i i=turnP i U (fun j=> if i=j then 1 else 0):= by unfold turnP; simp [mul_ite]; -- etc
      rw [show (1+V) i=(fun j=> if i=j then 1 else 0)+(V i) from funext fun j=> by simp [Matrix.one_apply], pair_turn]; rw [← he]
   rw [produces V hB0, augment Y h f (fun i=> bound_sum _ _ (fun j _=> bound_pair (costs_row i j) (HV i j))) (fun i j hij=> omit_sum _ _ _ fun k _ => omit_prod _ (shut_row i j k hij) (hv j i k)) (Finset.univ) hx (fun i _ => ht i) ]; -- defeq etc
   unfold f; simp_rw [ht']; rw [generated (1+V),mul_assoc]; unfold crown; apply finale Y h _ (bound_pair ?_ hx) (fun i hi=> omit_prod _ (?_) (ht i))
   · rw [Matrix.det_apply]; refine bound_sum _ _ fun j _=> bound_sign (Equiv.Perm.sign j:ℤ) _ (bound_prod _ _ (fun i _=>?_)) -- sign int sign Perm -> Equiv.Perm.sign j
     rw [Matrix.add_apply,Matrix.one_apply]; apply bound_add _ (HV _ _); split; exact bound_one; exact bound_zero
   rw [Matrix.det_apply]; refine omit_sum _ _ _ fun σ _=> shut_sign _ (Equiv.Perm.sign σ:ℤ) _ (omit_many _ _ _ (fun i _=>?_)); rw [Matrix.add_apply,Matrix.one_apply]; apply omit_add _ _ (hv _ _ _); split; exact omit_one _; exact omit_zero _
end
end YM.FVA2.Paper
