import YM.SchemeRG11.Sew.Weld
/-! Combining one OPEN port with several closed peers, cost membranes.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt
open scoped Classical
variable {I J K U:Type*} [DecidableEq I] (D:Dose U ℝ)
lemma mediate (s:Finset I)(p:I→ Paper U ℝ)(g:U→ℝ): vent g (∏ i∈s,p i)=∑i∈s, vent g (p i)*∏j∈s.erase i,p j:=by induction s using Finset.induction_on with
 | empty=>rw [Finset.prod_empty,(vent _).map_one_eq_zero,Finset.sum_empty]
 | insert i s hi ih=>
   rw [Finset.prod_insert hi,vent_l, Finset.sum_insert hi,Finset.erase_insert hi, mul_comm (vent g (p i)), ih,Finset.mul_sum,add_comm]; congr 1; apply Finset.sum_congr rfl; intro j hj
   have he:i≠ j:=fun p=>hi (p.symm ▸ hj); rw [Finset.erase_insert_of_ne he
                  ,Finset.prod_insert]; rw [mul_left_comm]; exact fun h=>hi (Finset.mem_of_mem_erase h)

variable (L:I→ J→K→ Stem U ℝ)(S:Subalgebra ℝ (J→ℝ))(Z:Set (J→ Stem U ℝ)) (s:Finset I)
def authorized :Prop:=∀ i∈s,∀ k:K,(fun x=> L i x k)∈ Z
def links(G:Gauge) := G -- remove
abbrev priceS :=∀i∈s,∀j∈s,i≠j→∀ (v w:K),(fun x=>D.bed (L i x v) (L j x w))∈ S
omit [DecidableEq I] in
lemma neigh(L:I→J→K→Stem U ℝ)(x:J)(i:I)(j:I)(k:K)(p:I→Paper K ℝ):
 let G:=vent (D.windfall (L i x k)); let F:=fun u:K=>D.bed (L i x k) (L j x u)
 G (D.neg.heat (vary (L j x) (p j)))=D.neg.heat (vary (L j x) (vent F (p j))):=by intro G F; unfold G; rw [D.neg.wind,varyVent];rfl
lemma pen(D : Dose U ℝ)(s:Finset I)(L:I→J→K→Stem U ℝ)(p:I→Paper K ℝ)(i:I)(hi:i∉s)(q: Paper K ℝ)(x:J):screen D (insert i s) L (Function.update p i q) x= D.neg.heat (vary (L i x) q)*screen D s L p x:=by
 unfold screen; rw [Finset.prod_insert hi, Function.update_self]; apply congrArg; apply Finset.prod_congr rfl; intro j hj
 rw [Function.update_of_ne (show j≠i from fun He=>hi (He ▸ hj))]
lemma sailgate(h:authorized L Z s)(hr:priceS D L S s)(p:I→Paper K ℝ)(A:array J U)(hA:Gate D S Z A): (fun x=> D.avg (D.neg.heat (A x)*screen D s L p x))∈S:=by
 induction s using Finset.induction_on generalizing A p with
 | empty=>simp only [screen,Finset.prod_empty,mul_one,Dose.prune]; exact hA [] fun i w=> List.not_mem_nil w |>.elim
 | insert i s hi IH=>
    have hu:authorized L Z s:=fun i hi=> h i (Finset.mem_insert_of_mem hi)
    have hv:priceS D L S s:=fun i hi j hj=>hr i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hz (q:Paper K ℝ)(f:I→Paper K ℝ)(A:array J U)(hA:Gate D S Z A): (fun x=>D.avg (D.neg.heat (A x)* (D.neg.heat (vary (L i x) q)*screen D s L f x)))∈S:=by
       induction q using MvPolynomial.induction_on generalizing A f with
       | C c=>
         have he(x:J):D.avg (D.neg.heat (A x)* (D.neg.heat (vary (L i x) (C c))*screen D s L f x))= c • D.avg (D.neg.heat (A x)*screen D s L f x):=by rw [vary_C,Dose.heat_C,C_mul',mul_smul_comm,map_smul]
         simp_rw [he]; exact S.smul_mem (IH hu hv f A hA) _ -- check args
       | add a b r q=> simp only [_root_.map_add,add_mul, mul_add]; exact S.add_mem (r f A hA) (q f A hA)
       | mul_X a k hh=>
         let w(x):= L i x k; let F:= fun x=> D.windfall (w x); let u(x:J):= D.neg.heat (vary (L i x) a); let v:= fun x=>D.neg.heat (A x); let Q:= screen D s L f
         have e(x:J): D.avg (D.neg.heat (A x)*(D.neg.heat (vary (L i x) (a*X k))* screen D s L f x))= D.avg (D.neg.heat (Sew.Strain D w A x) * (u x*Q x))+ D.avg (v x * (u x*vent (F x) (Q x))):=by
            rw [_root_.map_mul (vary _), vary_X]; change D.avg (v x*(D.neg.heat (_*leaf (w x))* Q x))=_
            rw [mul_left_comm (v x), mul_comm _ (leaf (w x)), fondle,vent_l,mul_add,map_add]; unfold u; rw [add_comm]
            apply congrArg₂
            · apply congrArg D.avg; rw [Sew.Strain,←Dose.wind]; unfold v; ring
            congr 1; ring
         simp_rw [e]; refine S.add_mem (hh f (Sew.Strain D w A) (Gate.rose D hA (h i (Finset.mem_insert_self ..) _))) ?_
         -- vent through screen
         let T (j:I)(x:J):=vent (F x) (D.neg.heat (vary (L j x) (f j)))
         have hsum (x:J):D.avg (v x*(u x*vent (F x) (Q x)))=∑ j∈s, D.avg (v x*(u x*(T j x* screen D (s.erase j) L f x))):=by unfold Q T screen; rw [mediate,Finset.mul_sum,Finset.mul_sum,map_sum]
         simp_rw [hsum]; change _∈S
         let V (j:I)(x:J):= D.avg (v x*(u x*(T j x* screen D (s.erase j) L f x)))
         rw [show (fun x=>∑ j∈s,_)=∑j∈s,V j from funext fun x=> (Finset.sum_apply x s V).symm]; apply Subalgebra.sum_mem; intro j hj
         obtain ⟨N,hN⟩:=North.itinerary (f j)
         let W(t:K):=update f j (vent (basisU t) (f j)); let Y(t:K)(x:J):=D.bed (w x) (L j x t)
         let U (t:K)(x:J):= D.avg (v x* (u x * screen D s L (W t) x))
         have Hx(x:J): V j x= ∑ t∈N, Y t x* U t x:=by
             change D.avg (v x*(u x*(vent (F x) _*_))) = _; unfold F w; rw [neigh]
             rw [hN N (Finset.Subset.refl _) (fun _=>1) (by simp)]
             simp only [one_mul,map_sum,map_smul,Finset.sum_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht
             have he : screen D s L (W t) x = D.neg.heat (vary (L j x) (vent (basisU t) (f j)))* screen D (s.erase j) L f x:=by -- fill
                generalize hm:s.erase j=s'; rw [show s= insert j s' from hm ▸ Eq.symm (Finset.insert_erase hj)]; unfold W; rw [pen D s']; rw [←hm]; simp
             unfold U Y; rw [he]; rw [smul_mul_assoc,mul_smul_comm, mul_smul_comm,map_smul];rfl
         rw [show V j=∑t∈N,Y t*U t from ?_]; apply Subalgebra.sum_mem; intro t _; exact S.mul_mem (hr _ (Finset.mem_insert_self ..) _ (Finset.mem_insert_of_mem hj) (fun he=>hi (he ▸ hj)) _ _) (hh _ A hA)
         funext x; rw [Finset.sum_apply]; exact Hx x
    have Hx(j:J): screen D (insert i s) L p j=D.neg.heat (vary (L i j) (p i))*screen D s L p j:=by unfold screen; rw [Finset.prod_insert hi]
    simp_rw [Hx]; apply hz _ p _ hA
end YM.SchemeRG11.Sew
