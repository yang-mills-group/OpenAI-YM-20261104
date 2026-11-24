import YM.SchemeRG11.Cover.Heat
/-! Real Wick subtraction respects ordinary slot-degree, strictly lowers in nonidentity term. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Labels
open Pert MvPolynomial SchemeRG11.Haze
open scoped ContDiff Classical BigOperators
variable {I J:Type} {d e:ℕ}
local notation "R"=> MvPolynomial I ℝ
section rite
variable [AddCommMonoid J]
/-- after Theater.measureN -/
lemma hetero (D:I→J)(H:J→R→Prop)(q:(I→₀ℕ))(z:ℝ)(hc:H 0 ( MvPolynomial.C z ))(hv:∀ x i (f:R),IsWeightedHomogeneous D f x → H x f → H (D i+x) ( MvPolynomial.X i*f )): H (Finsupp.weight D q) ( MvPolynomial.monomial q z ):= by
 induction q using Finsupp.induction with
 | zero=> rw [_root_.map_zero]; exact hc
 | @single_add a e p _ he h=>
     have hx (e:ℕ): H ( Finsupp.weight D ( Finsupp.single a e+p ) ) ( monomial ( Finsupp.single a e+p ) z ):= by
         induction e with | zero=> simpa using h | succ e iH=>
             have he : Finsupp.single a (e+1)+p= Finsupp.single a 1+(Finsupp.single a e+p):= by rw [ Finsupp.single_add ]; abel
             rw [he,_root_.map_add, Finsupp.weight_apply ];
             obtain ht:= hv _ a _ ( show IsWeightedHomogeneous D ( monomial ( Finsupp.single a e+p ) z ) _ from MvPolynomial.isWeightedHomogeneous_monomial D _ z rfl ) iH; convert! ht using 1
             · simp
             rw [ MvPolynomial.X, MvPolynomial.monomial_mul ]; simp
     exact hx e
lemma paradigm (D:I→J)(H:J→R→Prop){v:J}{p:R}(h:IsWeightedHomogeneous D p v)(hc:∀ c,H 0 (C c))(hz:∀ i,H i 0)(hv:∀ x i (f:R),IsWeightedHomogeneous D f x → H x f→ H (D i+x) ( X i*f ))(hf: ∀ x (f g:R), IsWeightedHomogeneous D f x→ IsWeightedHomogeneous D g x → H x f→ H x g→ H x ( f+g )): H v p:= MvPolynomial.IsWeightedHomogeneous.induction_on (motive:=fun p _=> H v p) (hz _) ( hf v ) (fun d c he=> he ▸ hetero D H d c ( hc c ) hv ) h
end rite
lemma vent_node (v:I→ℝ)(d:ℕ){p:R}(h:p.IsHomogeneous d): (vent v p).totalDegree ≤ d:= by
 refine paradigm (fun _=>1) (fun j:ℕ => fun p:R => (vent v p).totalDegree ≤ j) h (fun c=>?_) (fun w=>?_) (fun j i u hu ht=>?_) ?_
 · simp_rw [vent_C,totalDegree_zero]; exact le_rfl
 · rw [_root_.map_zero,totalDegree_zero]; exact Nat.zero_le _
 · rw [mul_comm,vent_x]; refine (totalDegree_add _ _).trans (max_le ?_ ((totalDegree_mul _ _).trans ?_))
   · exact (totalDegree_smul_le _ _).trans ((IsHomogeneous.totalDegree_le (show u.IsHomogeneous j from hu)).trans (by omega))
   rw [totalDegree_X]; omega
 intro j p q _ _ hp hq; rw [_root_.map_add]; exact (totalDegree_add _ _).trans (max_le hp hq)
lemma vent_below (v:I→ℝ)(p:R)(h:p.totalDegree≤d): (vent v p).totalDegree ≤ d:= by
 conv_lhs=> rw [← p.support_sum_monomial_coeff]
 rw [_root_.map_sum]; apply (totalDegree_finsetSum ..).trans; apply Finset.sup_le (f:=fun i=>totalDegree (vent v (monomial i (coeff i p)))); intro i hi
 exact (vent_node v i.degree (isHomogeneous_monomial _ rfl)).trans ( Nat.le_trans ( by have he:=le_totalDegree hi; exact he ) h )
-- degree+1 slots strict. Use ∨ to cover constants.
def Low (p:R)(i:ℕ): Prop:= p.totalDegree < i ∨ p=0
variable {p q:MvPolynomial I ℝ}
lemma low_add (h:Low p d)(k:Low q d): Low (p+q) d:=by
 rcases h with h|rfl; swap; simpa using k
 rcases k with k|rfl; swap; rw [add_zero]; exact Or.inl h
 exact Or.inl ((totalDegree_add p q).trans_lt (max_lt h k))
variable (D:Dose I ℝ)
lemma diff_low (h:IsHomogeneous p d): Low (D.heat p - p) d:= by
 refine paradigm (fun _=>1) (fun d:ℕ => fun p:R => Low (D.heat p-p) d) h (fun c=>?_) (fun j=>?_) (fun j i u hu ht=>?_) (fun v p q _ _ hp hq=>?_) -- order
 · rw [D.heat_C,sub_self]; exact Or.inr rfl
 · rw [_root_.map_zero,sub_self]; exact Or.inr rfl
 · rw [show D.heat (X i*u)-(X i*u)=X i * (D.heat u-u)+ vent (D.pulse i) (D.heat u) from ?w ]; swap; · rw [mul_comm (X i) u,D.heat_x]; ring
   have He : (D.heat u).totalDegree ≤ j:= by
     have h':(D.heat u-u).totalDegree≤j:=by rcases ht with ht|ht; exact ht.le; rw [ht,totalDegree_zero]; exact Nat.zero_le _
     nth_rw 1 [ ← sub_add_cancel (D.heat u) u ]; exact (totalDegree_add _ _).trans (max_le h' (IsHomogeneous.totalDegree_le (show u.IsHomogeneous j from hu)))
   apply low_add
   · rcases ht with h|h; · refine Or.inl ( (totalDegree_mul _ _).trans_lt ?_ ); rw [totalDegree_X]; omega
     exact Or.inr (by rw [h,mul_zero])
   exact Or.inl ( (vent_below _ _ He).trans_lt (by omega) )
 rw [_root_.map_add, add_sub_add_comm]; apply low_add hp hq
lemma high_degree (h:p.IsHomogeneous d): (D.heat p).totalDegree≤d:=by
 rcases diff_low D h with H|H
 · conv_lhs=> rw [← sub_add_cancel (D.heat p) p]
   exact (totalDegree_add _ _).trans (max_le H.le h.totalDegree_le)
 rw [sub_eq_zero.mp H]; exact h.totalDegree_le
lemma high_component (h:p.IsHomogeneous d): homogeneousComponent d ( D.heat p )=p:= by
 rcases diff_low D h with H|H; · have he:= homogeneousComponent_eq_zero d _ H; rw [_root_.map_sub, homogeneousComponent_of_mem h,if_pos rfl] at he; exact sub_eq_zero.mp he
 rw [sub_eq_zero.mp H, homogeneousComponent_of_mem h,if_pos rfl]
end YM.FVAAlt2.Pairing
