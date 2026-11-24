import YM.WilsonCoeffUV.Step.Rebase
/-! X parity and unchanged normalization, even restriction of vacuum after
freeing scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function Matrix PowerSeries Filter Set
open scoped BigOperators ContDiff
variable {U R : Type*}
section
variable [AddCommGroup R] [Module ℝ R]
lemma mix_lead {A:Cost}(h: constantCoeff A=1)(P:Pal R U): mix A P 0=P 0 := by
  ext i j; have he:constantCoeff A⁻¹=1:= by simp [h]
  simp [mix,h,he]
lemma mix_pure {A:Cost}{P:Pal R U}(h:∀ i,Pure (P i)) (j): Pure (mix A P j) := fun i=> Smooth.sum fun a _=> (h a i).smul _
lemma mix_length {A:Cost}{P:Pal R U}{l}(h:shellK l P): shellK l (mix A P):= fun j r h'=> Finset.sum_eq_zero fun a ha=> by rw [h a r (by have := Finset.mem_range.mp ha; omega),smul_zero]

def PairP (P:Pal R U): Prop:= ∀ i r,i%2≠r%2→P i r=0
omit [Module ℝ R] in
lemma arm_r {i j:ℕ} (h:j%2≠i%2){r:Ten R U i}: shine r j=0:= shine_dark (by omega)
omit [Module ℝ R] in
lemma shell_lop {k}{P:Pal ℝ U}(h:shellK k P): shellK k (lop P):= by intro i j t; rw [lop, if_neg (by omega), h _ _ t]
omit [Module ℝ R] in
lemma pare_sum {P Q:Pal R U}(h:PairP P)(e:PairP Q): PairP (P+Q):= by intro i r b; simp_rw [Pi.add_apply,h i r b,e i r b,add_zero]
omit [Module ℝ R] in
lemma pare_sub {P Q:Pal R U}(h:PairP P)(e:PairP Q): PairP (P-Q):= by intro i r b; simp_rw [Pi.sub_apply,h i r b,e i r b,sub_zero]
end

def evenC (f:Cost) : Prop := ∀ i,i%2≠0→coeff i f=0
lemma even_one : evenC 1 := by intro i hi; simp [coeff_one]; omega
lemma even_mul {f g:Cost}(h:evenC f)(u:evenC g) : evenC (f*g) := by
  intro i hi; rw [coeff_mul]; apply Finset.sum_eq_zero; intro a ha
  have he:= Finset.mem_antidiagonal.mp ha; by_cases h':a.1%2=0
  rw [u a.2 (by omega),mul_zero]
  rw [h _ h',zero_mul]
lemma even_pow {f:Cost}(h:evenC f)(i:ℕ): evenC (f^i) := by induction i with
                                                            | zero=> rw [pow_zero]; exact even_one
                                                            | succ i ih=> rw [pow_succ]; exact even_mul ih h

lemma even_iff (f:Cost): evenC f ↔ evalNegHom f=f := by
  have he n : coeff n (evalNegHom f)= (-1)^n*coeff n f:= by simp [evalNegHom]
  constructor
  · intro h; ext n; rw [he]; by_cases hh:n%2=0
    · rw [Even.neg_one_pow (Nat.even_iff.mpr hh), one_mul]
    rw [h n hh,mul_zero]
  intro h i hi; have hv:=he i; rw [h, Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))] at hv; linarith
lemma even_smul {f:Cost}(u:evenC f)(c:ℝ): evenC (c•f) := fun i hi=>by rw [coeff_smul,u i hi,smul_zero]
lemma even_inv {f:Cost}(h:evenC f)(e:constantCoeff f=1): evenC f⁻¹ := by
  rw [even_iff]; apply (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [e]) : IsUnit f).mul_right_inj.mp
  conv_lhs=>arg 1; rw [← (even_iff f).1 h];
  rw [←map_mul,PowerSeries.mul_inv_cancel f (by simp [e]),map_one]
lemma even_pace {f:Cost}(h:constantCoeff f=1)(g:evenC f) : evenC (pace f):= by
  have hn: evenC (logOf f) := by
    rw [even_iff]; apply raise_inj _ (constantCoeff_logOf h)
    · rw [←raise_map evalNegHom (by simp) (constantCoeff_logOf h),raising_log h,(even_iff f).1 g]
    have ht : X∣evalNegHom (logOf f) := by have he:= map_dvd (evalNegHom (A:=ℝ)) (X_dvd_iff.mpr (constantCoeff_logOf h)); simpa using he
    exact X_dvd_iff.mp ht
  rw [even_iff, pace,raise_map _ (by simp) (by rw [constantCoeff_smul,constantCoeff_logOf h,smul_zero]), (even_iff _).1 (even_smul hn _)]
lemma even_back {f:Cost}(h:constantCoeff f=1)(g:evenC f) : evenC (back f) := by
  let R: Cost→+*Cost:= (substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (cc_old f))).toRingHom
  let F: Cost→+*Cost:= (substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (fresh_coeff f))).toRingHom
  have hx : R X=oldG f:= substAlgHom_X _
  have hX : F X=freshG f:= substAlgHom_X _
  have ht i : R (C i)=C i := by change (substAlgHom _ _) = _; rw [coe_substAlgHom]; exact subst_C i
  have hy i : F (C i)=C i := by change (substAlgHom _ _) = _; rw [coe_substAlgHom]; exact subst_C i
  have he : F (oldG f)=X:= by change substAlgHom _ _ = _; rw [coe_substAlgHom]; exact reverse_right h
  have he' : R (freshG f)=X:= by change substAlgHom _ _ = _; rw [coe_substAlgHom]; exact reverse_left h
  have hb : F.comp R=RingHom.id _ := serial_ext (by rw [RingHom.comp_apply,hx,he];simp) (fun i=>by rw [RingHom.comp_apply,ht,hy]; rfl) (by rw [RingHom.comp_apply,hx,he]; rfl)
  have hN: R.comp evalNegHom=evalNegHom.comp R:= by
    have HN i: evalNegHom (C i:Cost)=C i:= by ext n; simp only [evalNegHom,coeff_rescale,coeff_C]; split_ifs with h <;> simp [*]
    have hg: evalNegHom (oldG f)= -(oldG f):= by rw [oldG,map_mul,(even_iff _).1 (even_pace h g),evalNegHom_X]; ring
    apply serial_ext (by rw [RingHom.comp_apply,evalNegHom_X,map_neg,hx,map_neg,cc_old,neg_zero]) (fun i=>by rw [RingHom.comp_apply,RingHom.comp_apply,HN,ht,HN]) (by rw [RingHom.comp_apply,evalNegHom_X,map_neg,hx,RingHom.comp_apply,hx,hg])
  have hl : R (evalNegHom (freshG f))= -(X):=Eq.trans (DFunLike.congr_fun hN (freshG f)) (by rw [RingHom.comp_apply,he',evalNegHom_X])
  have hr : evalNegHom (freshG f)= -(freshG f):= by
    have hZ: F (R (evalNegHom (freshG f)))= evalNegHom (freshG f):=DFunLike.congr_fun hb _
    rw [hl,map_neg,hX] at hZ; exact hZ.symm
  rw [even_iff]; apply mul_right_cancel₀ (b:=-(X:Cost)) (neg_ne_zero.mpr X_ne_zero)
  conv_lhs=> arg 2; rw [← evalNegHom_X]
  rw [←map_mul,mul_neg,fresh_back,hr]

lemma pair_mix {R:Type*}[AddCommGroup R][Module ℝ R]{P:Pal R U}(h:PairP P){A}(hc:constantCoeff A=1)(he:evenC A): PairP (mix A P) := by
  intro i r ht; apply Finset.sum_eq_zero; intro j hj
  by_cases h':j%2=r%2
  · rw [even_mul (even_pow he j) (even_pow (even_inv he hc) r) _ (by have := Finset.mem_range.mp hj; omega),zero_smul]
  rw [h _ _ h',smul_zero]
end YM.WilsonCoeffUV.Blue
