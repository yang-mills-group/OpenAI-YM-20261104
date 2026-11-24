import YM.SchemeRG11.Banner.Calm
/-! Ward gradients crossing => only finite surviving verticals. Price
 the actual triangular pilot. Per finite field horizon at actual T. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Banner
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial Outlook North Long
open scoped Classical Pointwise
variable {G:Gauge}{n d j:ℕ}{T: Align.Itinerary}{B:Window}{R:ℝ}
def curtain {n:ℕ}(v:Size G n):Prop:= ∀ i∈v.support,lineP i
lemma holiest (a:Size G n)(q:Sketch G n): (horizontal n q).coeff a= if curtain a then q.coeff a else 0:=by
 have he (s:Size G n)(c:ℝ):horizontal n (monomial s c)=if curtain s then monomial s c else 0:=by
   rw [MvPolynomial.monomial_eq,map_mul]; simp only [Finsupp.prod,map_prod,map_pow,horizontal,aeval_C,aeval_X, algebraMap_eq]
   split
   · next h=> congr 1; apply Finset.prod_congr rfl; intro i hi; rw [if_pos (h i hi)]
   next h=> apply mul_eq_zero_of_right; unfold curtain at h; push Not at h; obtain ⟨i,w,h⟩:=h; apply Finset.prod_eq_zero w; rw [if_neg h,zero_pow (Finsupp.mem_support_iff.mp w)]
 induction q using MvPolynomial.induction_on' with
 | monomial s c=>
    rw [he]; by_cases h:a=s
    · subst s; split <;> simp_all
    rcases Classical.em (curtain s) with h'|h'<;>simp [Ne.symm h,h'] -- parser
 | add p q hp hq=>rw [map_add,coeff_add,coeff_add, hp,hq]; split <;> simp
lemma amber (p:pLabel G)(v:Neutral p)(h:IsWeightedHomogeneous generation p d)(hb:B.rOut< R)(a:Size G n): Tendsto (fun i:ℕ=> T.gap i* MvPolynomial.coeff a (spume p v (gateY T R i) (cove T B i) d n).val) atTop (𝓝 0):=by
 simp only [spume,keeps_i]; by_cases he:rankW inkAge a ≤ d
 · simp only [he,↓reduceIte, holiest]; by_cases hw:curtain a
   · simp only [hw,↓reduceIte]; exact skimP (p:=p) h hb (by exact_mod_cast he)
   simp [hw]
 simp [he]
lemma bills (a:Size G n)(x:Sky G n):bill (a+Finsupp.single x 1)=bill a+inkAge x:=by unfold bill rankW; rw [map_add,Finsupp.weight_single,one_smul,Nat.cast_add]
lemma winders {I: Type*}[DecidableEq I](i:I) (a:I→₀ℕ)(q:Paper I ℝ): MvPolynomial.coeff a (vent (basisU i) q)= q.coeff (a+Finsupp.single i 1)*((a i:ℝ)+1):=by
 rw [show vent (basisU i) = pderiv i from ?_,MvPolynomial.coeff_pderiv]
 ext j; simp [Haze.vent,basisU,Pi.single_apply,eq_comm]
lemma melts (a:Size G n) (hv:¬curtain a) (p:pLabel G)(h:IsWeightedHomogeneous generation p d)(hb:B.rOut<R): Finishes (fun i=> (T.gap i)^(bill a-d)*coeff a (inlay G n (nebula (cove T B i) (gateY T R i) p))) :=by
 unfold curtain at hv; push Not at hv; obtain ⟨v,hm,H⟩:=hv
 let f:= a-Finsupp.single v 1
 have hh : 0<a v:= Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hm)
 have He:f+Finsupp.single v 1=a:=tsub_add_cancel_of_le (fun i=>by by_cases h:i=v<;> simp [h]; exact hh)
 have hr:bill a=bill f+inkAge v:= (congrArg bill He.symm).trans (bills ..)
 obtain ⟨q,Q,E,e⟩:=formatI v H; obtain ⟨t,U⟩:= verticalI n p
 let b:ℝ:= (f v:ℝ)+1
 have hq:= (Finishes.const b⁻¹).mul (fateful h hb f (θ:=q) (T:=T) Q)
 apply hq.same; filter_upwards [rank_zero (T:=T) (s:=t) hb, escort_cut (T:=T) hb] with i hi wi
 let s:=gateY T R i; let χ:= cove T B i; let M:= nebula χ s p
 change b⁻¹ * _ =_
 rw [← U χ s wi hi.1 hi.2 v q E e, winders, He,hr]; have ht :b≠0:=by unfold b; positivity
 change b⁻¹*(_*(_*b))=_; field_simp; rfl

def crestF (p:pLabel G)(T: Itinerary)(B:Window)(R:ℝ)(i:ℕ):= nebula (cove T B i) (gateY T R i) p
def margin (p:pLabel G)(T: Itinerary)(B:Window)(R:ℝ)(n d:ℕ)(i:ℕ):Sketch G n:= cliff inkAge d (inlay G n (crestF p T B R i))-cliff inkAge d (horizontal n (inlay G n (crestF p T B R i)))
lemma spike (a:Size G n)(p:pLabel G)(h:IsWeightedHomogeneous generation p d)(hb:B.rOut<R): Finishes (fun i=> (T.gap i)^(bill a-d)* coeff a (margin p T B R n d i)):=by
 simp only [margin,coeff_sub,keeps_i,holiest]; by_cases ha:rankW inkAge a≤d
 · simp only [ha,↓reduceIte]; by_cases he:curtain a
   · simp only [he,↓reduceIte,sub_self,mul_zero]; exact Finishes.const _
   simp only [he,↓reduceIte,sub_zero]; exact melts a he p h hb
 simp only [ha,↓reduceIte,sub_self,mul_zero]; exact Finishes.const _
lemma lim_s (p:pLabel G)(v:Neutral p) (h:IsWeightedHomogeneous generation p d) (hb:B.rOut<R) (F:Eidolon (G:=G) n d→ₗ[ℝ] ℝ): Tendsto (fun i=> T.gap i * F (spume p v (gateY T R i) (cove T B i) d n)) atTop (𝓝 0):=by
 -- extend F via evaluations Fin Many
 let V:=(Eidolon (G:=G) n d)
 let U: Set (Size G n):={a| rankW inkAge a≤ d}
 haveI : Finite U:= width_finite inkAge d (fun i=> Nat.le_add_left 1 _); letI:=Fintype.ofFinite ↥U
 let H: V→ₗ[ℝ](U→ℝ):= LinearMap.pi (fun i=> MvPolynomial.lcoeff ℝ i.val ∘ₗ V.subtype)
 obtain ⟨g,L⟩:= LinearMap.exists_leftInverse_of_injective H (LinearMap.ker_eq_bot'.mpr (by
    intro q h; apply Subtype.ext; ext a; by_cases he:a ∈ U
    · exact congrFun h (⟨a,he⟩:U)
    rw [Submodule.coe_zero,MvPolynomial.coeff_zero]; by_contra! hw; exact he ((MvPolynomial.mem_restrictSupport_iff ℝ).mp (show q.val∈ Ladder n d from q.property.1) (mem_support_iff.mpr hw)))) -- type?
 let C:= LinearMap.toContinuousLinearMap (F ∘ₗ g)
 let r(i:ℕ):= spume p v (gateY T R i) (cove T B i) d n
 have ht : Tendsto (fun i=> T.gap i • H (r i)) atTop (𝓝 0):= tendsto_pi_nhds.mpr fun i=> amber p v h hb i.val
 have he:= C.continuous.continuousAt.tendsto.comp ht
 rw [C.map_zero] at he; apply he.congr; intro i; change C (T.gap i • _) =_; rw [C.map_smul]; congr 1; exact congrArg F (LinearMap.congr_fun L _)
end YM.SchemeRG11.Banner
