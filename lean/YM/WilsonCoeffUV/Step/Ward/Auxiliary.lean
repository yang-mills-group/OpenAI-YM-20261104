import YM.WilsonCoeffUV.Step.Ward.HaarJac
/-! Algebra for lifting auxiliary substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries Filter Set
open scoped BigOperators Topology ContDiff
variable {X Y Z:Type*} (a:X→Ink (X⊕Z))(u:Y→Ink Z)
lemma reroll_X: reroll u a PowerSeries.X=PowerSeries.X := train_X _
lemma reroll_param : (reroll u a).comp (holdUp X)= (holdUp X).comp (train u) := by
  apply serial_ext (by simp only [RingHom.comp_apply,hold_X',reroll_X,constantCoeff_X]) _ (by simp only [RingHom.comp_apply,train_X,hold_X',reroll_X]); intro p
  have h (j:Y) : (reroll u a).comp (holdUp X) (path j)=holdUp X (train u (path j)) := by
    rw [RingHom.comp_apply,up_var,reroll,train_path, train_path]; rfl
  induction p using MvPolynomial.induction_on with
  | C r=> change reroll u a (holdUp X (realS r))=holdUp X (train u (realS r)); rw [reroll,hold_real,train_real,train_real,hold_real]
  | add v w a b=> simp_rw [map_add,a,b]
  | mul_X p j t=> simp only [map_mul,t,show C _=path j from rfl,h]; rfl
lemma reroll_up (r:Ink Y) : reroll u a (holdUp X r)=holdUp X (train u r):= DFunLike.congr_fun (reroll_param a u) r
lemma floor_pres {U:Type*}{T : Ink X→+*Ink U}(hx:T PowerSeries.X=PowerSeries.X){p:Ink X}(h:constantCoeff p=0) : constantCoeff (T p)=0 := PowerSeries.X_dvd_iff.mp (hx ▸ map_dvd T (PowerSeries.X_dvd_iff.mpr h))
lemma floor_const {U:Type*}{T : Ink X→+*Ink U}(hx:T PowerSeries.X=PowerSeries.X){p:Ink X}(h:constantCoeff p=1) : constantCoeff (T p)=1 := by
  have he := floor_pres (p:=p-1) hx (by rw [map_sub,h,map_one,sub_self]); rw [map_sub,map_one, map_sub,map_one] at he; exact sub_eq_zero.mp he
lemma floor_Exp {U:Type*}{T : Ink X→+*Ink U}(hx:T PowerSeries.X=PowerSeries.X){p:Ink X}(h:constantCoeff p=1): T (logOf p)=logOf (T p) := by
  have ht:=floor_const hx h
  apply raise_inj (floor_pres hx (constantCoeff_logOf h)) (constantCoeff_logOf ht); rw [← raise_map _ (by rw [hx]; simp) (constantCoeff_logOf h), raising_log h,raising_log ht]
lemma income (u:X→Ink Y)(c:PowerSeries ℝ): train u (soil c)=soil c := by
  let K:= (train u).comp soil
  have hx: K PowerSeries.X= PowerSeries.X:= by simp [K, soil]
  have h : K=soil:= serial_ext (by rw [hx]; simp) (fun i=>by change train u (PowerSeries.map _ _) = PowerSeries.map _ _; rw [map_C,map_C]; apply train_real) (by rw [hx]; simp [soil]); exact DFunLike.congr_fun h c
variable [Fintype X] [DecidableEq X]
def fanWest (u:Y→Ink Z): Ink (X⊕Y)→+* Ink (X⊕Z):= railCov (1:Matrix X X ℝ) u
lemma fan_reroll : fanWest (X:=X) u=reroll u (fun i=>path (Sum.inl i)) := by
  simp_rw [fanWest,railCov]; unfold reroll; congr 2; exact funext fun i=> unit_pin i
lemma body_along : fanWest (X:=X) (Y:=Y) u (bodyQ Y (1:Matrix X X ℝ))=bodyQ Z 1 := form_rotate u 1 (by simp)
lemma body_tee (K:Matrix X X ℝ): fanWest u (bodyQ Y K)=bodyQ Z K := form_rotate u 1 (by simp)
lemma param_int [Fintype Y] [Fintype Z] (u:Y→Ink Z){H:Matrix X X ℝ}(h:H.transpose=H)(p:Ink (X⊕Y)): Wick Z H (fanWest u p)=train u (Wick Y H p) := W_linear 1 u h h (by simp) _

omit [DecidableEq X] in
lemma moment_const (ϑ:X→Ink (X⊕Z))(G:Matrix X X ℝ) (v:Y→Ink Z)(i:X): reroll v ϑ (slopeQ Y G i)=∑ j,G i j • ϑ j := by
  unfold slopeQ; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [reroll, train_smul, train_path]; rfl

section lead
variable [Fintype Z]
omit [Fintype X] [DecidableEq X] [Fintype Z] in
private lemma moment_head {x:X}{A B:Ink (X⊕Z)}(h:constantCoeff A=constantCoeff B) : constantCoeff (brush (.inl x) A)=constantCoeff (brush (.inl x) B):= by rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,brush,blot_apply,blot_apply]; simp only [coeff_zero_eq_constantCoeff_apply,h]
-- no need Fintype Y. use direct differentiation of body.
omit [Fintype Z] in
private lemma callH (a:X→Ink (X⊕Z))(u:Y→Ink Z)(K:Matrix X X ℝ)(hk:K.transpose=K)(j:X)[Fintype Y] : brush (.inl j) (reroll u a (bodyQ Y K))= ∑ i:X, brush (.inl j) (a i)*∑ b: X,K i b • a b := by
  rw [reroll,reroutes,Fintype.sum_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr,Function.comp_apply, up_vacant,zero_mul, Finset.sum_const_zero,add_zero]
  change ∑ i, _ * reroll u a _= _
  apply Finset.sum_congr rfl; intro i _; rw [body_derived K hk, moment_const]
omit [DecidableEq X] in
private lemma pull_lead (R:Matrix X X ℝ)(q:Lawn (X⊕Z)→ Lawn X)(hR:R=edgeM q 0)(i j:X)(hq:Green q)(hz:q 0=0) :
    constantCoeff (brush (Sum.inl j) (spool q i))=MvPolynomial.C (R i j):= by rw [spool_ext q i hq hz (Sum.inl j), jet_lead, hR]; rfl

lemma strike_leading (u:Y→Ink Z)[Fintype Y]
   (q:Lawn (X⊕Z)→ Lawn X)(hq:Green q)(hz:q 0=0) (K:Matrix X X ℝ)(hK:K.transpose=K)(hk:IsUnit K.det)
   (R:Matrix X X ℝ)(hR:R=edgeM q 0)(hr:IsUnit R.det)
   (c d:Ink Z)
   (hc:constantCoeff (bodyQ Z K + holdUp X c)=constantCoeff (reroll u (spool q) (bodyQ Y K)+ holdUp X d)) :
   K= R.transpose*K*R ∧ ∀ i, constantCoeff (spool q i)=constantCoeff (noiseLine R i) := by
  let v:=spool q
  -- gradient one
  have first (j:X): constantCoeff (slopeQ Z K j)=constantCoeff (∑ i:X, brush (.inl j) (v i)*(∑ b:X,K i b • v b)) := by
    have h:= moment_head (x:=j) hc; rw [map_add (brush _),map_add (brush _),up_vacant,up_vacant,add_zero,add_zero,body_derived _ hK,callH _ _ _ hK] at h; exact h
  let A j:= constantCoeff (v j)
  let C:=MvPolynomial.C (σ:=X⊕Z) (R:=ℝ)
  have S j {a: Ink (X⊕Z)}: constantCoeff (brush (Sum.inl j) a)=MvPolynomial.pderiv (.inl j) (constantCoeff a) := by rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,brush,blot_apply]
  have e₁ j : ∑ i, K j i • MvPolynomial.X (Sum.inl (β:=Z) i) = ∑ i, C (R i j) * ∑ b:X, K i b • A b := by
    have H:=first j; simp_rw [slopeQ,map_sum,constantCoeff_smul,path, constantCoeff_C,map_mul,map_sum,constantCoeff_smul, show ∀ i,constantCoeff (brush (.inl j) (v i))=C (R i j) from fun i=>pull_lead R q hR i j hq hz] at H; exact H
  have hh (i j) : MvPolynomial.pderiv (.inl j) (A i)= C (R i j):= (S j).symm.trans (pull_lead R q hR i j hq hz)
  have e₂ : K= R.transpose*K*R := by
    ext1 i j
    classical
    have he:=congrArg (MvPolynomial.pderiv (Sum.inl j)) (e₁ i); simp_rw [map_sum, Derivation.map_smul,MvPolynomial.pderiv_mul, map_sum,Derivation.map_smul,hh] at he
    simp only [C,MvPolynomial.pderiv_C,zero_mul,zero_add] at he
    rw [Finset.sum_eq_single j] at he;
    · simp only [MvPolynomial.pderiv_X_self, Algebra.smul_def,mul_one,MvPolynomial.algebraMap_eq] at he
      apply MvPolynomial.C_injective (σ:=X⊕Z) (R:=ℝ)
      rw [he,Matrix.mul_apply]; simp only [Matrix.mul_apply,transpose_apply,map_sum, Finset.mul_sum, Finset.sum_mul,map_mul]
      rw [Finset.sum_comm]; simp_rw [mul_assoc]
    · intro b _ hb; rw [MvPolynomial.pderiv_X_of_ne (by simpa), smul_zero]
    simp
  refine ⟨e₂,?_⟩
  let B (a:X): POL (X⊕Z) := MvPolynomial.X (.inl a)
  have h : K.map C *ᵥ B= (R.map C).transpose *ᵥ ((K.map C)*ᵥ A) := by
    ext1 i; simpa only [mulVec,dotProduct, Matrix.map_apply,transpose_apply,C, Algebra.smul_def,MvPolynomial.algebraMap_eq] using e₁ i
  have e : K.map C=(R.map C).transpose*(K.map C)*(R.map C) := by
    conv_lhs=>rw [e₂];
    simp_rw [Matrix.map_mul]; rfl
  conv_lhs at h=> rw [e,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  let D := (R.map C).transpose * (K.map C)
  have hu : IsUnit D.det:= by unfold D; rw [Matrix.det_mul, Matrix.det_transpose]; change IsUnit ((C.mapMatrix R).det * (C.mapMatrix K).det); rw [← RingHom.map_det, ← RingHom.map_det]; exact (hr.map C).mul (hk.map C)
  conv_lhs at h=> rw [Matrix.mulVec_mulVec]
  conv_rhs at h=> rw [Matrix.mulVec_mulVec]
  have eq: A = (R.map C)*ᵥ B := by
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hu) h.symm
  intro i
  change A i=_; rw [eq]; simp_rw [noiseLine,map_sum,constantCoeff_smul,path,constantCoeff_C]; simp only [B,dotProduct,mulVec,Matrix.map_apply,C, Algebra.smul_def,MvPolynomial.algebraMap_eq]
end lead
end YM.WilsonCoeffUV.Blue
