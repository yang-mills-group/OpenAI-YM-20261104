import YM.SchemeRG11.Cover.Breathe
/-! At the finite Orb, can replace the actual Gaussian Taylor rules
 even for negative-metric auxiliary Wick terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial MeasureTheory ProbabilityTheory Pert Warp
open scoped Classical
variable {J I B E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ:Measure E) [IsGaussian μ]
def clouds (f : I→ E→L[ℝ] ℂ): Dose I ℂ:= ⟨fun i j=> ∫ x:E,f i x*f j x ∂μ,fun i j=>by congr 1; funext x; ring⟩
variable (f : I→ E→L[ℝ] ℂ) (h : ∀ i,∫ x:E,f i x ∂μ=0)
def value (p : Paper I ℂ) (x:E):= aeval (fun i=>f i x) p
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma value_tame (p:Paper I ℂ): Orb.Tame (value f p):=by
 induction p using MvPolynomial.induction_on with
 | C a=> unfold value; simp only [aeval_C]; exact Orb.Tame.constant _
 | add a b ha hb=> unfold value; simp only [map_add]; exact Orb.Tame.add ha hb
 | mul_X a i ih=> unfold value; simp only [map_mul,aeval_X]; exact Orb.Tame.mul ih (Orb.Tame.clm (f i))
def cash : Paper I ℂ→ₗ[ℂ] ℂ where
 toFun p:=∫ x:E,value f p x ∂μ
 map_add' a b:=by unfold value; simp only [map_add]; exact integral_add (price_tame μ (value_tame f a)) (price_tame μ (value_tame f b))
 map_smul' c p:=by unfold value; simp only [map_smul,RingHom.id_apply]; apply integral_smul
lemma cash_eq (p:Paper I ℂ): cash μ f p=∫ x:E,value f p x ∂μ:=rfl
lemma escort (D:Dose I ℂ)(g:B→I)(s:Finset B)(i:B)(hi:i∈s):
 let m (t:Finset B):=∏ j∈t,(X (g j):Paper I ℂ)
 let Z : Finset B→ℂ:=fun t=> D.avg (m t)
 Z s=∑ j∈s.erase i,D.pulse (g i) (g j)*Z ((s.erase i).erase j):=by
 intro m Z; unfold Z
 have hm:m s = (m (s.erase i))*X (g i):=Eq.symm (Finset.prod_erase_mul _ _ hi)
 let v j: Stem I ℂ:= Finsupp.single (g j) 1
 have he W:m W=∏ j∈W,leaf (v j):=by simp [leaf,m,v]
 have hu j:sense (D.pulse (g i)) (v j)=D.pulse (g i) (g j):=by simp [sense,v]
 rw [hm,D.release]; simp_rw [he,taste_prod _ _ v,hu,map_sum,map_smul]; rfl
include h in
lemma cruise [Fintype B] (g:B→I)(s:Finset B): cash μ f (∏ i∈s,X (g i))=(clouds μ f).avg (∏ i∈s,X (g i)):=by
 let D:=clouds μ f
 let a (i:B):E→L[ℝ] ℂ:=f (g i)
 let A(s:Finset B):=∏ i∈s,(X (g i):Paper I ℂ)
 have he (s):cash μ f (A s)=kick μ s (fun i:B=> fun x:E=> a i x):=by simp [cash_eq,A,kick,value,a]
 change cash μ f (A s)=_
 induction s using Finset.strongInduction with | H s hs =>
   by_cases hp:s.Nonempty
   · have hw:D.avg (A s) * (s.card:ℂ)=∑ i∈s,∑ j∈s.erase i,D.pulse (g i) (g j)*D.avg (A ((s.erase i).erase j)):=by
       rw [Finset.sum_congr rfl (g:=fun _=>D.avg (A s)) (fun i hi => (escort D g s i hi).symm),Finset.sum_const,nsmul_eq_mul,mul_comm]
     apply mul_right_cancel₀ (b:=(s.card:ℂ)) (by have he : s.card>0:= Finset.card_pos.mpr hp; exact_mod_cast he.ne')
     have hb:=exchange_s μ s a (fun j _=> h _)
     change cash μ f _ * _=D.avg (A s)*_
     rw [hw,he,mul_comm,← nsmul_eq_mul,hb]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j _; rw [←he]; congr 1
     exact hs _ (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hi))
   rw [Finset.not_nonempty_iff_eq_empty.mp hp]; simp [A,cash_eq,value]
-- extend across polynomial via monomial basis
include h in
theorem contract : cash μ f=(clouds μ f).avg :=by
 apply Module.Basis.ext (MvPolynomial.basisMonomials I ℂ)
 intro m
 let Q:= (a : ↑m.support) × Fin (m a.val)
 let g: Q→I:=fun i=> i.1.val
 have he : MvPolynomial.basisMonomials I ℂ m=∏ i:Q,(X (g i):Paper I ℂ):=by
   rw [show (MvPolynomial.basisMonomials I ℂ m)=(MvPolynomial.monomial m (1:ℂ)) from rfl,MvPolynomial.monomial_eq,map_one,one_mul,Finsupp.prod, ← Finset.prod_attach]
   unfold Q g; rw [Fintype.prod_sigma]; simp
 rw [he]; exact cruise μ f h g _
lemma cash_products (h0 : ∀ i,∫ x:E,f i x ∂μ=0) (D:Dose I ℂ)(hk : ∀ i j,∫ x:E,f i x*f j x ∂μ=D.pulse i j)(p:Paper I ℂ): cash μ f p=D.avg p:=by
 rw [contract μ f h0]; unfold clouds; congr!
 exact hk ..
end YM.SchemeRG11.Haze
