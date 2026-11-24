import YM.WilsonCoeffUV.Step.Ward.Invariance

/-!
# Parameter-preserving kinetic reset

Ψ(t) converting towards older coupling. `mix` uses rank weights because the
logs are simultaneously changed! Signs and projection readouts on true
curvature to provide f afterwards, drop scalar there. f is NOT the actual
numeric calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function Matrix PowerSeries Filter Set
open scoped BigOperators
variable {U V R:Type*}

abbrev Cost := PowerSeries ℝ
def tailS (f:Cost) : Cost := mk fun n=>coeff (n+1) f
@[simp] lemma tail_rank (f:Cost)(n) : coeff n (tailS f)=coeff (n+1) f := coeff_mk ..
lemma tail_X {p:Cost}(h:constantCoeff p=0): tailS p * X=p := by
  ext i; cases i<;> simp [h]

/-- inverse ratio for sqrt U(t) using zero constant logOf. Multiply LAST. -/
def pace (f:Cost) : Cost:= raiseE ((-(1/2:ℝ)) • (logOf f))
lemma pace_cc {f:Cost}(h:constantCoeff f=1): constantCoeff (pace f)=1 := raise_one (by rw [constantCoeff_smul,constantCoeff_logOf h,smul_zero])
lemma raise_still (R:Type*) [CommRing R][Algebra ℚ R][IsAddTorsionFree R]: raiseE (0:PowerSeries R)=1 := by
  apply raise_unique _ (raise_change (map_zero _)) (by simp); rw [raise_one (map_zero _),map_one]
lemma pace_tax {f:Cost}(h:constantCoeff f=1): f * (pace f)^2=1 := by
  let n:Cost:=logOf f
  have hu:=raising_log h; have H:constantCoeff n=0:=constantCoeff_logOf h
  set r:=-(1/2:ℝ)
  have he : constantCoeff (r•n)=0:= by rw [constantCoeff_smul,H,smul_zero]
  change f*raiseE (r•n)^2=1
  rw [show f=raiseE n from hu.symm, pow_two, ←raise_add he he,← raise_add H (by simp [he]), ← add_smul,show n+(r+r) • n=0 from ?a,raise_still]
  case a => have h : r+r= -1:=by unfold r; ring
            rw [h,neg_smul,one_smul]; simp
lemma pace_substitution {A:Cost}(h:constantCoeff A=1): IsUnit (coeff 1 (pace A * X)) := by rw [show coeff 1 _ = _ from coeff_succ_mul_X 0 (pace A), coeff_zero_eq_constantCoeff_apply,pace_cc h]; simp

def oldG (f:Cost) := pace f * X
def freshG (f:Cost) : Cost := if h:constantCoeff f=1 then (oldG f).substInvOfIsUnit (pace_substitution h) else X
def back (f:Cost) := tailS (freshG f)
lemma fresh_coeff (f:Cost): constantCoeff (freshG f)=0:= by rw [freshG]; split<;>simp
lemma fresh_back {f:Cost}: back f * X=freshG f := tail_X (fresh_coeff _)
lemma back_cc {f:Cost}(h:constantCoeff f=1) : constantCoeff (back f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,back,tail_rank,freshG, dif_pos h,coeff_one_substInvOfIsUnit]
  have he : (pace_substitution h).unit=1 := by ext; rw [IsUnit.unit_spec]; simp [pace_cc h]
  change (↑((pace_substitution h).unit⁻¹):ℝ)=1
  rw [he]; simp
lemma cc_old (f:Cost): constantCoeff (oldG f)=0 := by simp [oldG]
lemma reverse_right {f:Cost}(h:constantCoeff f=1) : (oldG f).subst (freshG f)=X := by rw [freshG,dif_pos h, PowerSeries.subst_substInvOfIsUnit_right _ (cc_old f)]
lemma reverse_left {f:Cost}(h:constantCoeff f=1) : (freshG f).subst (oldG f)=X := by rw [freshG,dif_pos h, PowerSeries.subst_substInvOfIsUnit_left _ (cc_old f)]

-- bookkeeping ratio in the target variable
lemma bridge_price {f:Cost}(h:constantCoeff f=1) : f.subst (freshG f)*(back f)⁻¹ ^2=1 := by
  let A:=freshG f; let B:=back f; let r:=PowerSeries.substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (fresh_coeff f));
  have hf : ∀ p:Cost,r p=subst A p:=fun i=>congr_fun (coe_substAlgHom (HasSubst.of_constantCoeff_zero' (fresh_coeff f))) i
  have he : (r (pace f): Cost)* (r X)=X:= by rw [←map_mul]; exact (hf _).trans (reverse_right h)
  rw [show r X=A from substAlgHom_X _, show A=B*X from (fresh_back).symm,← mul_assoc] at he
  have ht : B * ((r (pace f)):Cost)=1 := by rw [mul_comm]; exact mul_right_cancel₀ (b:=X) X_ne_zero (by rw [he]; simp)
  have hx : (r (pace f):Cost)= B⁻¹ := by
    apply (isUnit_iff_constantCoeff.mpr (by rw [back_cc h]; simp) : IsUnit B).mul_right_inj.mp
    rw [ht,PowerSeries.mul_inv_cancel B (by rw [back_cc h]; simp)]
  rw [←hf, show (back f)⁻¹=(r (pace f):Cost) from hx.symm];
  refine (Eq.trans ?h (by rw [pace_tax h,map_one]: r (f*pace f^2)= (1: Cost)))
  case h=> rw [map_mul,map_pow]

-- redo substitutes whole action p. c old/new ratio *input*.
def redo (A:Cost) : Ink U →+* Ink U:=
  edit (MvPolynomial.aeval (R:=ℝ) (fun i:U=> soil A⁻¹ * path i)).toRingHom (x:=soil A * X) (by simp)
lemma redo_X (A:Cost) : redo (U:=U) A X=soil A * X := by rw [redo,edit_X]
lemma redo_path (A:Cost)(i:U) : redo A (path i)=soil A⁻¹ * path i := by rw [redo,path,edit_C]; simp [path]
lemma redo_base (A:Cost)(c:ℝ) : redo (U:=U) A (realS c)=realS c := by change redo _ (C (MvPolynomial.C _))= _; rw [redo,edit_C]; simp [real_alg]
lemma redo_μ (A:Cost)(c:ℝ)(p:Ink U): redo A (c•p)=c • redo A p:= by rw [Algebra.smul_def,map_mul,real_alg,redo_base,Algebra.smul_def,real_alg]

section finite
variable [Fintype U]
lemma redo_palm (A:Cost){r}(T:Ten ℝ U r) : redo A (C (paint _ T))=(soil A⁻¹)^r * C (paint r T):= by
  have he i (u :POL U): C (i•u)=(i:ℝ) • C u := by rw [Algebra.smul_def,Algebra.smul_def,real_alg,map_mul, MvPolynomial.algebraMap_eq]; rfl
  simp only [paint,palm_form,map_sum,he,map_sum,redo_μ,map_prod,(fun i:U=>show C (MvPolynomial.X i)=path i from rfl), redo_path,Finset.mul_sum,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_smul_comm]

/-- graded only through own e. No ext rank changes. -/
def mix [SMul ℝ R] [AddCommMonoid R] (A:Cost) (P:Pal R U) : Pal R U := fun j r=>∑ i∈Finset.range (j+1), coeff (j-i) (A^i*(A⁻¹)^r) • P i r
lemma redo_stern (A:Cost){P:Pal ℝ U}{n}(h:shellK n P) : redo A (flash P)=flash (mix A P) := by
  apply PowerSeries.ext; intro j
  have hz : constantCoeff (redo (U:=U) A X)=0:=by rw [redo_X]; simp
  rw [filtered hz (shave (flash P) (j+1)) j j.lt_succ_self];
  have he i (hi:i∈Finset.range (j+1)): still (P i) (n+j+1):= by
    intro r hr; have he:i<j+1:= Finset.mem_range.mp hi; exact h i r (by omega)
  let S:= Finset.range (n+j+1)
  have hS : still (mix A P j) (n+j+1):= fun r hr=> Finset.sum_eq_zero fun i hi=> by rw [he i hi r hr,smul_zero]
  rw [map_sum,map_sum, flash]
  simp only [map_mul,map_pow,coeff_mk,redo_X,mul_pow]
  rw [flash,coeff_mk,visible hS]; simp_rw [mix,map_sum,map_smul]; conv_rhs=> rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi; rw [visible (he i hi)]; simp_rw [map_sum,redo_palm,Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro r _;
  rw [show (soil A⁻¹)^r * C (paint r _) * (soil A^i * X^i) = (soil (A^i*(A⁻¹)^r)*C (paint r (P i r)))*X^i by rw [map_mul,map_pow,map_pow]; ring, coeff_mul_X_pow',if_pos (by have he:= Finset.mem_range.mp hi; omega), coeff_mul_C,Algebra.smul_def,soil,coeff_map]; rfl
lemma redo_jet (A:Cost)(h:constantCoeff A=1)(f:Lawn U→ℝ): redo A (jet f)=jet f:= by
  apply PowerSeries.ext; intro n
  have hz : constantCoeff (redo (U:=U) A X)=0:=by rw [redo_X]; simp
  rw [filtered hz (shave (jet f) (n+1)) n n.lt_succ_self]
  have he: (soil (U:=U) A⁻¹)*soil A=1:= by rw [←map_mul,PowerSeries.inv_mul_cancel A (by rw [h];simp),map_one]
  have hx i: redo A (C (coeff i (jet f)) * X^i)= C (coeff i (jet f)) * X^i := by
    rw [map_mul,map_pow,jet_apply,redo_X,redo_palm,mul_pow]; calc
      _= (soil (U:=U) A⁻¹ * soil A)^i*(C (paint _ (rye f i))*X^i):= by rw [mul_pow]; ring
      _= _:= by rw [he]; simp
  simp_rw [map_sum,hx]; rw [←map_sum]; exact (shave (jet f) _ _ n.lt_succ_self).symm

lemma spool_reset [Fintype V](f:Lawn U→Lawn V)(h:f 0=0)(A:Cost)(u:constantCoeff A=1)(i):
    redo A (spool f i)=soil A⁻¹ * spool f i := by
  have he: (soil (U:=U) A)*soil A⁻¹=1:= by rw [←map_mul,PowerSeries.mul_inv_cancel A (by rw [u];simp),map_one]
  apply mul_left_cancel₀ (a:=soil A * X) (mul_ne_zero (left_ne_zero_of_mul (b:=_) (by rw [he]; simp)) X_ne_zero)
  conv_lhs=> arg 1; rw [←redo_X]
  rw [←map_mul, spool_raised _ h,redo_jet _ u]
  conv_rhs=> rw [mul_comm _ X, mul_assoc,←mul_assoc (soil A),he,one_mul,spool_raised _ h]
lemma redo_com [Fintype V](A:Cost)(u:constantCoeff A=1)(f:Lawn U→Lawn V)(h:f 0=0) : (redo A).comp (train (spool f))=(train (spool f)).comp (redo A) := by
  let T:=spool f; let J:= (redo A).comp (train T); let K:= (train T).comp (redo A)
  have hx : J X=soil A*X:= by unfold J; rw [RingHom.comp_apply,train_X,redo_X]
  have hX : K X=soil A*X:= by unfold K; rw [RingHom.comp_apply,redo_X,map_mul,train_X]; congr 1; apply income
  change J=K
  apply serial_ext (by rw [hx]; simp) _ (hx.trans hX.symm); intro p
  induction p using MvPolynomial.induction_on with
  | C a=> change redo A (train T (realS a))=train T (redo A (realS a)); rw [train_real,redo_base,redo_base,train_real]
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p j a=> rw [map_mul C,map_mul J,map_mul K,a]; refine congrArg (K (C p) * ·) (show J (path j)=K (path j) from ?_); change redo A (train (spool f) (path j))=train _ (redo A (path j)); rw [train_path,spool_reset f h A u,redo_path,map_mul,income,train_path]

end finite
end YM.WilsonCoeffUV.Blue
