import YM.X.Rank.Motion
/-!
The finite-alphabet heat contraction formula and its use on arbitrary coupling
kernels. Extend polynomials by finite support; eventual equality here is literal.
Also useful outside the rank calculations in PT.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Heat
open Function Set Filter Maxwell Rank Next.Rank.Normal MvPolynomial
open scoped Topology BigOperators Classical
variable {V : Type*}
local notation "K"=> Next.Rank.Normal.Symmetric
abbrev D (x: V → ℂ) : Module.End ℂ (poly V) := (slit x).toLinearMap
lemma Da (x: V → ℂ)(p:poly V): D x p=slit x p:=rfl
def therm (s:Finset V)(q:K V) : Module.End ℂ (poly V) := (1/2:ℂ) • ∑ i∈s,D (q.cov i) * D (Pi.single i 1)
def plume (L:Module.End ℂ (poly V))(n:ℕ) : Module.End ℂ (poly V):= ∑ j∈Finset.range n, (j.factorial:ℂ)⁻¹ • L^j
variable (s:Finset V)(q:K V)(x:V→ℂ)
lemma commute : Commute (D x) (therm s q):= by
  apply LinearMap.ext; intro u
  change D x ((therm s q) u)= therm s q (D x u); simp only [therm,LinearMap.smul_apply,LinearMap.sum_apply,map_sum,map_smul, Module.End.mul_apply]
  apply congr_arg; refine Finset.sum_congr rfl ?_; intro i hi; simp only [Da]; rw [show slit x (slit (q.cov i) _) =_ from slit_slit _ _ _, show slit x (slit _ u)=_ from slit_slit _ _ _]
lemma heating {v:V} (h:v∈s){p:poly V}(hp:p∈ supported ℂ (s:Set V)) :
    therm s q (X v * p)=X v * therm s q p + slit (q.cov v) p := by
  have he(i:V): D (q.cov i) (D (Pi.single i 1) (X v*p))=X v * (D (q.cov i) (D (Pi.single i 1) p))+ (q.cov v i • D (Pi.single i 1) p + if i=v then D (q.cov i) p else 0):= by
    simp only [Da]; rw [slit_prod, map_add, slit_prod, Derivation.leibniz, slit_C]; simp only [q.symm i v]
    split_ifs with hz
    · rw [hz]; simp only [← C_mul',Pi.single_eq_same,C_1,smul_eq_mul,mul_zero,one_mul]; ring
    simp only [Pi.single_eq_of_ne (show v≠i from Ne.symm hz),← C_mul',C_0,smul_eq_mul]; ring
  let L := therm s q; let T:= fun v:V=>D (q.cov v)*D (Pi.single v 1)
  have hz : ∑ i∈s, q.cov v i • D (Pi.single i 1) p = slit (q.cov v) p := by
    conv_lhs => arg 2; intro i; rw [show D (Pi.single i 1) p=pderiv i p from slit_single i p];
    exact (slit_flat _ _ _ (mem_supported.mp hp)).symm
  simp_rw [therm,LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply, he]; rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hz, ← Finset.mul_sum]; simp only [Finset.sum_ite_eq',h,↓reduceIte]; rw [show D (q.cov v) p= _ from Da _ p]; simp only [mul_smul_comm]; module -- edit
lemma holds {p:poly V} (hp:p∈supported ℂ (s:Set V)) (n:ℕ) : ((therm s q)^n) p ∈ supported ℂ (s:Set V) := by
  induction n with
  | zero=> rw [pow_zero,Module.End.one_apply]; exact hp
  | succ n ih=> rw [pow_succ', Module.End.mul_apply]; let T:=supported ℂ (s:Set V); have he : ∀ f:poly V,f∈ T → therm s q f ∈ T:= fun f hf=> by rw [therm,LinearMap.smul_apply, LinearMap.sum_apply]; exact T.toSubmodule.smul_mem _ (T.toSubmodule.sum_mem (fun i hi=> slit_stays _ (slit_stays _ hf))); -- edit
                exact he _ ih
lemma thermal {v:V} (h:v∈s){p:poly V}(hp:p∈ supported ℂ (s:Set V))(n:ℕ) :
    ((therm s q)^(n+1)) (X v * p)=X v * ((therm s q)^(n+1)) p + ((n+1:ℕ):ℂ) • slit (q.cov v) (((therm s q)^n) p) := by
  let L:=therm s q
  induction n with
  | zero=> simpa only [Nat.reduceAdd,pow_one, pow_zero, Nat.cast_one, one_smul] using! heating s q h hp
  | succ n ih=>
    have hc : L (slit (q.cov v) ((L^n) p))= slit (q.cov v) ((L^(n+1)) p):= (DFunLike.congr_fun (commute s q (q.cov v)).eq _).symm.trans (by rw [pow_succ']; rfl) -- edit
    change ((L^((n+1)+1)) _) = _
    nth_rw 1 [pow_succ']; change L (((therm s q)^(n+1)) _)=_
    rw [ih,map_add,heating s q h (holds s q hp (n+1)),map_smul,hc]
    rw [pow_succ' (therm s q) (n+1), Module.End.mul_apply]; unfold L; push_cast; module

lemma flowing (p:poly V)(hp:p∈supported ℂ (s:Set V)) : ∀ᶠ n:ℕ in atTop, (therm s q^n) p=0 ∧ (plume (therm s q) (n+1)) p = milk q p := by
  let L:=therm s q
  have ht : (p.vars:Set V) ⊆ range ((↑):↥s→V) := fun i hi=> ⟨⟨i,(mem_supported.mp hp hi)⟩,rfl⟩
  obtain ⟨P,rfl⟩:= MvPolynomial.exists_rename_eq_of_vars_subset_range p ((↑):↥s→V) Subtype.val_injective ht; clear hp ht
  induction P using MvPolynomial.induction_on with
  | C a=>
    let p:= C (σ:=V) a; have h (n:ℕ): (L^(n+1)) p=0:= by rw [pow_succ, Module.End.mul_apply, show L p=0 from ?_, map_zero]; unfold L; simp only [therm,p,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,Da,slit_C,map_zero,Finset.sum_const_zero,smul_zero]
    simp_rw [rename_C]; filter_upwards [eventually_gt_atTop 0] with n hn; cases n; contradiction; rename_i n; refine ⟨h n,?_⟩
    change plume L _ p= _; rw [plume,LinearMap.sum_apply,Finset.sum_range_succ',fine]; simp_rw [LinearMap.smul_apply,h]; simp [p]
  | add a b ha hb=> filter_upwards [ha,hb] with n ha hb; rw [map_add]; exact ⟨by rw [map_add,ha.1,hb.1,add_zero],by rw [map_add,ha.2,hb.2,map_add]⟩
  | mul_X p i ih=>
    rw [map_mul,rename_X,mul_comm _ (X ..)]; let w:=i.val; let Q:= rename ((↑):↥s→V) p; have hQ : Q∈ supported ℂ (s:Set V):= by rw [supported_eq_range_rename]; exact ⟨p,rfl⟩ -- lift defeq?
    have hA j:(L^(j+1)) (X w*Q)= X w*(L^(j+1)) Q + ((j+1:ℕ):ℂ) • slit (q.cov w) ((L^j) Q):= thermal s q i.property hQ j
    obtain ⟨k,hk⟩:= eventually_atTop.mp ih; filter_upwards [eventually_ge_atTop (k+1)] with j hj; cases j; omega
    rename_i j; obtain ⟨hz,H⟩:= hk j (by omega); obtain ⟨hz',H'⟩:= hk (j+1) (by omega)
    change (L^ (j+1)) (X w*Q) = 0 ∧ plume L ((j+1)+1) (X w*Q)= _
    constructor
    · rw [hA,hz',hz,mul_zero,map_zero,smul_zero,zero_add]
    unfold plume; rw [LinearMap.sum_apply,Finset.sum_range_succ']; simp_rw [LinearMap.smul_apply,hA, smul_add]; rw [Finset.sum_add_distrib,feeds, ← show plume L ((j+1)+1) Q= milk q Q from H', show plume L ((j+1)+1) Q= plume L (j+1) Q from H'.trans H.symm]
    have hd : plume L (j+1+1) Q=plume L (j+1) Q:= H'.trans H.symm
    conv_rhs=> lhs; rhs; rw [← hd,plume, LinearMap.sum_apply,Finset.sum_range_succ']
    unfold plume; simp_rw [LinearMap.sum_apply,map_sum,LinearMap.smul_apply,Derivation.map_smul]
    have heq (i:ℕ): ((Nat.factorial (i+1):ℂ))⁻¹ * ↑(i+1:ℕ)=(Nat.factorial i:ℂ)⁻¹:= by rw [Nat.factorial_succ, Nat.cast_mul]; field_simp
    simp only [smul_smul,heq,pow_zero,L,Module.End.one_apply,Nat.factorial_zero,w, Nat.cast_one,inv_one,one_smul] -- factorial expands heq too? 
    rw [mul_add,Finset.mul_sum]; simp_rw [mul_smul_comm]; abel
end YM.PositionX.Heat
