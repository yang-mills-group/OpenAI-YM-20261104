import YM.FormalBulk08.Avenue.Flux
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free Reef Orb Wick Series Jets Lava Gauge
open Stationary hiding Rays
open MvPolynomial
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {V U W:Type} [Fintype V] [Fintype U] [Fintype W]
abbrev Pce (V:Type):=Glyphs ℝ V
variable (q D : Matrix V V ℝ)

lemma padder (p:Pce V)(k:ℕ)(hp:p.totalDegree≤k): hearth q p= ∑ i∈Finset.range (k+1), (ounce ℝ i) • (press q ^ i : Module.End ℝ _) p:= by
    rw [hearth_def,show bake q p=heatLetter q p from rfl,heatLetter,Polynomial.eval_finsetSum]; simp only [Polynomial.eval_monomial,one_pow,mul_one]; refine Finset.sum_subset (Finset.range_mono (by omega)) (?_); intro i hi h'; rw [press_nilpotent q p i (by simp only [Finset.mem_range] at hi h'; omega),smul_zero]
lemma hearth_flux (p: Pce V)(x:V): hearth q (pderiv x p)=pderiv x (hearth q p):= by
    let k:=p.totalDegree; rw [padder q _ k ((pderiv_degree _ p).trans (Nat.sub_le ..)),padder q p k le_rfl,_root_.map_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Derivation.map_smul]; apply congr_arg; clear hi
    induction i with
    | zero=>rfl
    | succ i ih => rw [pow_succ',Module.End.mul_apply,Module.End.mul_apply]; rw [ih,press_commutes]
-- induction on total
lemma hearth_equ (T: Pce V→ₗ[ℝ]Pce V) (h₁ : T 1=1)(h:q.IsSymm)(he:∀ p i,T (MvPolynomial.X i*p)=MvPolynomial.X i*T p+∑ j,C (q i j)*T (pderiv j p)): T=hearth q:= by
    apply LinearMap.ext; intro p
    suffices h : ∀ k : ℕ, ∀ x : Pce V, x.totalDegree ≤ k → T x=hearth q x from h _ _ (le_refl _)
    clear p; intro k; induction k using Nat.strong_induction_on with
    | _ k ih=>
     intro x hx
     conv_lhs => rw [x.as_sum];
     conv_rhs => rw [x.as_sum];
     simp_rw [_root_.map_sum]; apply Finset.sum_congr rfl; intro m hm
     by_cases hmm : m=0
     · subst m;change T (C _) = hearth q (C _)
       rw [show ∀ r:ℝ,MvPolynomial.C r=(r • (1 : Pce V)) from fun r=>by rw [MvPolynomial.smul_eq_C_mul,mul_one]]
       simp [h₁]
     obtain ⟨i,hi⟩ := Function.ne_iff.mp (show ⇑m ≠ (0 : V → ℕ) from fun he=> hmm (DFunLike.ext _ _ (congr_fun he)))
     let b:=m-Finsupp.single i 1
     have hh : Finsupp.single i 1+b=m := add_tsub_cancel_of_le ?_
     · have hA:= (le_totalDegree hm).trans hx
       nth_rw 1 [←hh] at hA; rw [Finsupp.sum_add_index' (fun _=>rfl) (fun _ _ _=>rfl)] at hA; simp at hA
       let P:=MvPolynomial.monomial b (MvPolynomial.coeff m x)
       have hz : P.totalDegree<k := lt_of_le_of_lt (totalDegree_monomial_le ..) (by exact lt_of_lt_of_le (Nat.lt_add_of_pos_left (by omega)) hA)
       have hw : (MvPolynomial.monomial m (MvPolynomial.coeff m x))=MvPolynomial.X i*P := by nth_rw 1 [← hh]; rw [monomial_single_add,pow_one]
       rw [hw,he,hearth_X q (fun i j=>Matrix.IsSymm.apply h j i),ih _ hz _ le_rfl]; congr 1;exact Finset.sum_congr rfl fun j _=> by rw [ih _ hz _ ((pderiv_degree j P).trans (Nat.sub_le ..))]
     intro j; by_cases hj:j=i
     · subst j; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero hi
     simp [hj]
lemma hearth_fire (f: Pce V)(hq:q.IsSymm)(hd:D.IsSymm): hearth q (hearth D f)= hearth (D+q) f:= by
    let T:= (hearth q).comp (hearth D); change T f=_; apply DFunLike.congr_fun; apply hearth_equ (D+q) T (?_) (hd.add hq);swap
    · show hearth q (hearth D 1)=_; simp
    intro p i; change hearth q (hearth D _)= _; simp_rw [hearth_X D (fun i j=> hd.apply j i),_root_.map_add,_root_.map_sum,hearth_X q (fun i j=>hq.apply j i),← hearth_flux]; rw [add_assoc,←Finset.sum_add_distrib]; change X i * T p+_= X i*T p+_; congr 1; apply Finset.sum_congr rfl; intro v _; rw [Matrix.add_apply,_root_.map_add, add_mul,show C (D i v) * ((hearth D) ((pderiv v) p))=_ from C_mul',map_smul]; rw [MvPolynomial.smul_eq_C_mul]; exact add_comm ..
lemma press_tow (L:Matrix U V ℝ) (t:Matrix U U ℝ)(h:L*q*Lᵀ=t)(p:Pce U): press q (mixRows L p)=mixRows L (press t p) := by
    subst t
    simp_rw [press_eq,pderiv_mix,_root_.map_sum,pderiv_mul, pderiv_C,zero_mul,zero_add,pderiv_mix, Matrix.mul_apply,Matrix.transpose_apply];
    -- reordering
    unfold halve
    simp only [Finset.sum_mul, Finset.mul_sum,_root_.map_sum,_root_.map_mul,mixRows, MvPolynomial.aeval_C,algebraMap_eq,← mul_assoc];
    -- sums orders on left i j v₂ v₁. aim v₂ v₁ i j, telescoped
    conv_lhs =>
      arg 2; ext x; arg 2; ext y; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    conv_lhs=> arg 2; ext x; rw [Finset.sum_comm]
    conv_lhs=> rw [Finset.sum_comm]
    conv_rhs=> arg 2; ext j; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro v _ ; apply Finset.sum_congr rfl; intro b _;ring
lemma hearth_mix (L:Matrix U V ℝ) (f:Pce U): hearth q (mixRows L f)=mixRows L (hearth (L*q*Lᵀ) f):= by
   let k:=max (mixRows L f).totalDegree f.totalDegree; rw [padder q _ k (le_max_left ..),padder (L*q*Lᵀ) f k (le_max_right ..),_root_.map_sum]; refine Finset.sum_congr rfl fun i hi=> ?_; rw [map_smul]; apply congr_arg
   clear hi; induction i with
   | zero=> rfl
   | succ i ih=>rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]; exact press_tow q L _ rfl _
end YM.FormalBulk08.Avenue
