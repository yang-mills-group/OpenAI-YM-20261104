import YM.XSpace.Strumming
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
/-! # Homogeneous operations on Gram probe tests -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {D J:Type*}[Fintype J] [DecidableEq J]
variable {p q:Channel D J}
namespace Hide
lemma ion (hp:Hide p) (a b:D→ℝ): Hide (ionic a b p):= fun l=> hp ((a,b)::l)
lemma trivial (D J:Type*) [DecidableEq J][Fintype J]: Hide (0:Channel D J):=by intro l; simp
lemma plus (hp:Hide p)(hq:Hide q):Hide (p+q):= by intro l; rw [map_add,map_add,hp,hq,zero_add]
lemma scale (hp:Hide p)(c:ℂ): Hide (c • p):= by intro l; rw [map_smul,map_smul,hp,smul_zero]
lemma minus (hp:Hide p)(hq:Hide q):Hide (p-q):= by intro l; rw [map_sub,map_sub,hp,hq,sub_self]
lemma void (hp:Hide p): MvPolynomial.aeval (0:D×J→ℂ) p=0:= hp []
lemma testSum {V:Type*} (v:V→Channel D J)(S:Finset V)(h:∀ i∈ S, Hide (v i)): Hide (∑ i∈S,v i):= by
  intro l; rw [map_sum, map_sum]; exact Finset.sum_eq_zero fun i hi=> h i hi l
end Hide
variable (p)

def baro (d:D)(a:D→ℝ)(p:Channel D J) : Channel D J:= ∑ j:J, X (d,j)*nex a j p

lemma revolver (a b v:D→ℝ)(d:D): ionic a b (baro d v p)=baro d v (ionic a b p)+(↑(a d):ℂ) • ionic v b p+(↑(b d):ℂ) • ionic a v p:=by
  have he j (u:D→ℝ) t (p:Channel D J): nex u j (X (d,t)*p)= X (d,t)*nex u j p+(if j=t then (↑(u d):ℂ) • p else 0):= by unfold nex; rw [Normal.slit_prod]; unfold electron; split_ifs <;> simp [*,C_mul']
  have hv (j t:J):
      nex b t (nex a t (X (d,j)*nex v j p))= X (d,j)*nex v j (nex b t (nex a t p))+(if t=j then ((b d:ℂ) • nex v j (nex a t p))+(a d:ℂ) • nex b t (nex v j p) else 0):= by
    rw [he,show nex a t (nex v j p)=nex v j (nex a t p) from Normal.slit_slit ..]
    have h (F K:Channel D J):nex b t (F+K)=nex b t F+nex b t K:= (slit _).map_add F K
    rw [h,he]; simp_rw [show nex b t (nex v j (nex a t p))=_ from (Normal.slit_slit _ _ _)]; split <;> simp [nex, *,add_assoc]
  rw [baro,map_sum]; simp only [ionic_val,hv,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold baro; unfold nex; simp_rw [map_sum,Finset.mul_sum, Finset.smul_sum]; abel

variable {p}
lemma Hide.rows (hp:Hide p) (d:D)(a:D→ℝ): Hide (baro d a p):= by
  intro L; induction L generalizing p with
  | nil=> change aeval _ (baro d a p)=0; simp [baro]
  | cons s l ih=> rcases s with ⟨u,v⟩; rw [tune_feed,revolver]; simp only [map_add,map_smul]; rw [ih (hp.ion u v),(hp.ion a v),(hp.ion u a)]; simp

def geo (c d:D):Channel D J:=∑ i:J, X (c,i)* X (d,i)
lemma ion_geo (a b:D→ℝ)(c d:D) (p:Channel D J):
    ionic a b (geo c d*p)= geo c d*ionic a b p +
      ((↑(a d):ℂ) • baro c b p+(↑(a c):ℂ) • baro d b p)+((↑(b d):ℂ) • baro c a p+(↑(b c):ℂ) • baro d a p)+
      ∑ _i:J, ((↑(a d):ℂ)*(↑(b c):ℂ)+(↑(a c):ℂ)*(↑(b d):ℂ)) • p:= by
  have hn (u:D→ℝ)(j:J)(p q:Channel D J):nex u j (p*q)=p*nex u j q+nex u j p*q:= by unfold nex; rw [(slit _).leibniz]; simp [smul_eq_mul,mul_comm q]
  have he (j:J)(f:D→ℝ): nex f j (geo c d) =(↑(f d):ℂ) • X (c,j)+(↑(f c):ℂ) • X (d,j):= by
    have hu(v:D) t:nex f j (X (v,t)) = if t=j then C (↑(f v):ℂ) else (0:Channel D J):= by unfold nex; rw [slit_X]; unfold electron; by_cases h:t=j <;> simp [*,Ne.symm]
    have hb:nex f j (geo c d)=∑ t:J,nex f j (X (c,t)*X (d,t):Channel D J):= map_sum (slit ..) _ _
    rw [hb]; simp_rw [hn, hu]; simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_add_distrib, Finset.sum_ite_eq',Finset.mem_univ,ite_true]; rw [← C_mul',← C_mul',mul_comm (X ..)]
  have hz(v w:Channel D J)(j:J): nex b j (v+w)=nex b j v+nex b j w:=(slit _).map_add v w
  have hw(j:J):nex b j (nex a j (geo c d))=C ((↑(a d):ℂ)*(↑(b c):ℂ)+(↑(a c):ℂ)*(↑(b d):ℂ)):= by rw [he,hz]; unfold nex; rw [(slit _).map_smul,(slit _).map_smul,slit_X,slit_X]; unfold electron; simp only [ite_true,map_add,map_mul,C_mul']
  rw [ionic_val]; simp_rw [hn,hz,hn,hw]; unfold baro; rw [ionic_val]; simp only [Finset.sum_add_distrib,Finset.mul_sum, Finset.smul_sum,he,C_mul', add_mul,smul_mul_assoc]; abel

lemma Hide.times (hp:Hide p)(c d:D): Hide (geo c d*p):= by
  intro L; induction L generalizing p with
  | nil=>change aeval (R:=ℂ) (0:D×J→ℂ) ((geo c d:Channel D J)*p)=0; rw [map_mul (aeval _)]; simp [geo]
  | cons a L ih=>
    obtain ⟨a,b⟩:=a; rw [tune_feed,ion_geo]; simp only [map_add,map_smul,map_sum]; rw [ih (hp.ion a b),hp.rows c b,hp.rows d b,hp.rows c a,hp.rows d a]; simp only [hp L,smul_zero, Finset.sum_const_zero,add_zero]
variable [Fintype D]

def innerDegree (D J:Type*)[Fintype D][Fintype J][DecidableEq J] (p:Channel D J):= ∑ d:D, baro d (Pi.single d 1) p
lemma inner_eq (p:Channel D J): innerDegree D J p = ∑ i:D × J, X i * pderiv i p := by
  have he (d:D)(j:J): Derivation.toLinearMap (slit (electron (Pi.single d 1) j)) = Derivation.toLinearMap (pderiv (R:=ℂ) (d,j)):= by
    suffices slit (electron (Pi.single d 1) j) = pderiv (d,j) by rw [this]
    ext1 i; obtain ⟨a,b⟩:=i; by_cases h:a=d <;> by_cases g:b=j <;> simp [electron,h,g,Ne.symm]
  unfold innerDegree baro nex; rw [Fintype.sum_prod_type]; simp_rw [show ∀ (d:D)(j:J), slit (electron (Pi.single d 1) j) p= pderiv (d,j) p from fun d j=> LinearMap.congr_fun (he d j) p]
lemma lapHide (p : Channel D J)(hp:Hide p) : Hide (∑ i:D×J,pderiv i (pderiv i p)):= by
  have h (d:D)(t:J) : pderiv (R:=ℂ) (d,t)=slit (electron (Pi.single d 1) t):= by ext1 i; obtain ⟨a,b⟩:=i; by_cases h:a=d <;> by_cases g:b=t <;> simp [electron,h,g,Ne.symm]
  rw [Fintype.sum_prod_type]; apply Hide.testSum; intro i _
  simp_rw [h]; have he:= hp.ion (Pi.single i 1) (Pi.single i 1); rw [ionic_val] at he; exact he

def spinD : Module.End ℂ (Channel D J):= ∑ i:D×J,(LinearMap.mulLeft ℂ (X i)).comp (pderiv i).toLinearMap
lemma spinD_val : spinD p=innerDegree D J p:= by simp only [inner_eq,spinD,LinearMap.sum_apply]; rfl
lemma spinHide (h:Hide p):Hide (spinD p):= by rw [spinD_val]; exact Hide.testSum _ _ (fun i _=> h.rows _ _)
lemma eulerD (p:Channel D J) (j:ℕ)(hp:p.IsHomogeneous j): spinD p=(j:ℂ) • p:= by rw [Nat.cast_smul_eq_nsmul ℂ j p,spinD_val,inner_eq]; exact hp.sum_X_mul_pderiv

lemma characteristic(S:Finset ℕ)(F:ℕ→Channel D J)(l:ℕ)(h:∀ i∈S,(F i).IsHomogeneous i)(hp: Hide (∑ i∈S,F i))(hL:l∈S): Hide (F l):= by
  induction S using Finset.strongInduction generalizing F with
  | H S IH =>
    by_cases hs:S={l}; · subst S; simpa using hp
    have hh : (S.erase l).Nonempty:= Finset.nonempty_iff_ne_empty.mpr (fun he=>hs (by nth_rw 1 [← Finset.insert_erase hL]; rw [he]; rfl))
    obtain ⟨i,hi⟩:= hh
    have ht:= Finset.mem_erase.mp hi
    let U:= S.erase i
    let Z (j:ℕ):=(j:ℂ)-(i:ℂ)
    have hx : spinD (∑ j∈S,F j)-(i:ℂ) • ∑ j∈S,F j = ∑ j∈U,Z j • F j:= by
      rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,← Finset.add_sum_erase _ _ ht.2]; rw [eulerD (F i) _ (h i ht.2),sub_self,zero_add]; apply Finset.sum_congr rfl; intro j hj; rw [eulerD (F j) _ (h j (Finset.mem_of_mem_erase hj)),← sub_smul]
    have hu : Hide _:= (spinHide hp).minus (hp.scale (i:ℂ)); rw [hx] at hu
    have he:= IH U (Finset.erase_ssubset ht.2) _ (fun j hj=> (homogeneousSubmodule (D × J) ℂ j).smul_mem _ (h j (Finset.mem_of_mem_erase hj))) hu (Finset.mem_erase.mpr ⟨ht.1.symm,hL⟩)
    have hy : Z l≠0:= sub_ne_zero.mpr (by exact_mod_cast ht.1.symm)
    change Hide (Z l • F l) at he; simpa only [smul_smul,inv_mul_cancel₀ hy,one_smul] using he.scale (Z l)⁻¹
end YM.XSpace.Stab
