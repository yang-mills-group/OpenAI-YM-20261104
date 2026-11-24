import YM.X.Braid.Stitch
import YM.PertExtension.HeatProjection
/-!
# Uniform totalDegree rank for shell insertions. Independent offsets heights. Real/scalar tape in Curly. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Plate
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension MeasureTheory Metric Filter Set Function Asymptotics Reed Braid
open scoped Topology ContDiff Classical BigOperators
variable {V W I:Type*} {p p' : poly V}{t:V→ℂ}{a:ℂ}{k m n:ℕ}
abbrev duty (p:poly V)(d:ℕ):= p.totalDegree ≤ d
namespace duty
lemma more (h:duty p k)(hk:k≤n):duty p n:= le_trans h hk
lemma add(h:duty p k)(hi:duty p' k):duty (p+p') k:= (totalDegree_add p p').trans (max_le h hi)
lemma scalar (a:ℂ)(h:duty p k):duty (a • p) k:= (totalDegree_smul_le ..).trans h
lemma zero:duty (0:poly V) k:=by simp [duty]
lemma base (a:ℂ): duty (MvPolynomial.C (σ:=V) a) k:= (totalDegree_C ..)|>.le |>.trans (Nat.zero_le _)
lemma one : duty (1:poly V) k:=by simp [duty]
lemma x (i:V):duty (MvPolynomial.X i) 1:= by simp [duty,totalDegree_X]
lemma mul (h:duty p k)(hi:duty p' m): duty (p*p') (k+m):= (totalDegree_mul ..).trans (Nat.add_le_add h hi)
lemma subs (h:duty p k)(hi:duty p' k): duty (p-p') k:= (totalDegree_sub ..).trans (max_le h hi)
lemma costs {f:I→poly V}(s:Finset I)(h:∀ i∈s,duty (f i) k):duty (∑ i∈s,f i) k:= (totalDegree_finsetSum ..).trans (Finset.sup_le h)
lemma toll (f:I→V)(s:Finset I):duty (glyphs f s) s.card:=by
    unfold glyphs; unfold duty; apply le_trans (totalDegree_finsetProd ..); simp [totalDegree_X]
-- common lift via simple letter tests of an arbitrary linear map
lemma lift {L:poly V→ₗ[ℂ] poly W}(p:poly V)(h:duty p k)(he:∀ i:ℕ,i≤k→∀ x:Fin i→V,duty (L (glyphs x Finset.univ)) (k+n)):duty (L p) (k+n):= by
    nth_rw 1 [p.as_sum];rw [map_sum]; refine duty.costs _ (fun i hi=>?_); rw [show monomial i (coeff i p)=coeff i p • monomial i (1:ℂ) from ?_,map_smul]; swap; · rw [←map_smul,smul_eq_mul,mul_one]
    apply duty.scalar; obtain ⟨v,H⟩:= Common.letter i; rw [H]; exact he _ ((le_totalDegree hi).trans h) v
lemma affine (F:poly V→ₐ[ℂ] poly W) (hf:∀ i:V,duty (F (X i)) 1) (hp:duty p k) : duty (F p) k:= by
    refine lift (k:=k) (n:=0) (L:=F.toLinearMap) _ hp (fun i hx v=> ?_); unfold glyphs; change duty (F _) (k+0); rw [map_prod]; unfold duty; apply le_trans (totalDegree_finsetProd ..); refine (Finset.sum_le_sum (g:=fun j=>1) fun j _=>hf _).trans ?_; simpa using hx
lemma deriv_p (p:poly V)(D:Derivation ℂ (poly V) (poly V))(h:∀ i:V,duty (D (X i)) k)(he:duty p n): duty (D p) (n+k):= by
    refine lift (L:= D.toLinearMap) p he (fun d hd t=> ?_); have hi(s:Finset (Fin d)): duty (D (glyphs t s)) (s.card+k):= by
       induction s using Finset.induction_on with
       | empty=> rw [glyphs,Finset.prod_empty,D.map_one_eq_zero]; exact duty.zero
       | insert i s hi IH=>
          unfold glyphs; rw [Finset.prod_insert hi,D.leibniz, Finset.card_insert_of_notMem hi]; change duty ((X (t i))*D (glyphs t s)+(glyphs t s)*D (X (t i))) _; apply duty.add; · exact ((duty.x _).mul IH).more (by omega)
          exact ((duty.toll _ s).mul (h _)).more (by omega)
    exact (hi Finset.univ).more (by simp [hd])
lemma slit_p (h:duty p k):duty (slit t p) k:= by refine duty.deriv_p (n:=k) (k:=0) _ _ ?_ h; intro i; rw [slit_X]; exact duty.base _
lemma milk_p (Q:Symmetric V)(h:duty p k): duty (milk Q p) k:= by
    rcases Nat.eq_zero_or_pos k with hk|hk; · rw [(Heat.degree_decrease Q p k h).1 hk];exact h
    nth_rw 1 [← sub_add_cancel (milk Q p) p]; exact duty.add ((Heat.degree_decrease Q p k h).2 hk|>.le) h
lemma knot_p (Q:Symmetric V)(h:duty p k)(hp:duty p' m):duty (knot Q p p') (k+m):= duty.milk_p Q ((h.milk_p _).mul (hp.milk_p _))
lemma hit_p (Q:Symmetric V)(h:duty p k)(hp:duty p' m): duty (hit Q p p') (k+m):= by rw [Nat.add_comm]; exact deriv_p _ _ (fun i=>by rw [hit_point]; exact h.slit_p) hp
lemma multi_p (Q:Symmetric V)(h:duty p k)(hp:duty p' m): duty (multi Q p p') (k+m):=((knot_p Q h hp).subs (h.mul hp)).subs (hit_p Q h hp)
end duty
end YM.PositionX.Plate
