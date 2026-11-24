import YM.XSpace.Coupler
/-! # Fischer detection via compact ball moments -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial

section weight
variable (n:ℕ) (r:ℝ)
-- compact support and radial recurrence, starting at exponent 1
private lemma hinge (x:ℝ): HasDerivAt (fun t:ℝ=> (max t 0)^(n+2)) (((n+2:ℕ):ℝ)*(max x 0)^(n+1)) x:= by
  rcases lt_trichotomy x 0 with h|h|h
  · rw [max_eq_right h.le,zero_pow (by omega),mul_zero]; refine HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const x 0) ?_; filter_upwards [gt_mem_nhds h] with t ht; rw [max_eq_right (le_of_lt ht),zero_pow (by omega)]
  · subst x; rw [← hasDerivWithinAt_univ,max_self,zero_pow (by omega),mul_zero,← show Iic (0:ℝ) ∪ Ici 0=_ from Set.Iic_union_Ici] -- inspect
    apply HasDerivWithinAt.union
    · apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr
      · intro z hz; rw [max_eq_right hz,zero_pow (by omega)]
      simp
    have hp: HasDerivAt (fun t:ℝ=>t^(n+2)) 0 0 := by simpa using (hasDerivAt_pow (n+2) (0:ℝ))
    apply hp.hasDerivWithinAt.congr
    · intro t ht; rw [max_eq_left ht]
    simp
  rw [max_eq_left h.le]
  refine HasDerivAt.congr_of_eventuallyEq (hasDerivAt_pow _ x) ?_; filter_upwards [lt_mem_nhds h] with t ht; rw [max_eq_left (le_of_lt ht)]

variable {A:Type*}[Fintype A]
def bowl (z:EuclideanSpace ℝ A):= (max (r^2-‖z‖^2) 0)^(n+1)
@[fun_prop] lemma bowl_cont: Continuous (bowl (A:=A) n r):= by unfold bowl; fun_prop
lemma bowl_support : HasCompactSupport (bowl (A:=A) n r):= by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:EuclideanSpace ℝ A) |r|); intro x hx; rw [Metric.mem_closedBall,dist_zero_right]
  by_contra! hr; exact hx (by unfold bowl; rw [max_eq_right,zero_pow (by omega)]; nlinarith [abs_nonneg r,sq_abs r])
lemma bend_bowl (x:EuclideanSpace ℝ A): DifferentiableAt ℝ (bowl (n+1) r) x ∧ ∀ v:EuclideanSpace ℝ A,
    fderiv ℝ (bowl (n+1) r) x v = (-2*(n+2:ℕ) :ℝ)*bowl n r x*inner ℝ x v:= by
  let w x:= max x (0:ℝ)
  have hp:= (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub (r^2)
  have h := ((hinge n _).hasFDerivAt.comp x hp)
  refine ⟨h.differentiableAt,fun v=>?_⟩
  rw [show fderiv ℝ (bowl (n+1) r) x=_ from h.fderiv]; simp [bowl, two_smul]; ring
end weight

section
variable {A:Type*} [Fintype A]
abbrev VectorA (A:Type*)[Fintype A]:= EuclideanSpace ℝ A
def watches (p:poly A)(x:VectorA A) := MvPolynomial.aeval (fun i=> (↑(x i):ℂ)) p
lemma watch_kin (p:poly A): ContDiff ℝ ∞ (watches p) := by
  induction p using MvPolynomial.induction_on with
  | C a=>rw [show watches (MvPolynomial.C (σ:=A) a)=fun _=>a from _root_.funext fun i=>by simp [watches]]; exact contDiff_const
  | add p q h H=> unfold watches; simp_rw [map_add]; exact h.add H
  | mul_X p i h=> unfold watches; simp_rw [map_mul, aeval_X]; exact h.mul (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)
lemma spin_eye (p:poly A) (i:A) (x:VectorA A): fderiv ℝ (watches p) x (EuclideanSpace.basisFun A ℝ i)=watches (pderiv i p) x := by
  let v:=EuclideanSpace.basisFun A ℝ i
  induction p using MvPolynomial.induction_on with
  | C a=>
    rw [pderiv_C]; unfold watches; simp
  | add p q h H=>
    rw [show watches (p+q)=watches p+watches q from _root_.funext fun i=>map_add .., fderiv_add ((watch_kin p).differentiable (by simp) _) ((watch_kin q).differentiable (by simp) _),add_apply,h,H]; simp [watches]
  | mul_X p j h=>
    let V:= Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜:=ℝ) j)
    rw [show watches (p*X j)=watches p*⇑V from _root_.funext fun i=>by simp only [watches,Pi.mul_apply,map_mul,aeval_X];rfl,fderiv_mul ((watch_kin p).differentiable (by simp) _) V.differentiableAt]; simp only [add_apply,V.fderiv,h,smul_apply]; by_cases hi:i=j <;> simp [*,V,watches,Ne.symm]

variable (n:ℕ) (r:ℝ)
def pool (f:VectorA A → ℂ) : ℂ:= ∫ x, bowl n r x • f x
lemma pooling {f:VectorA A → ℂ}(h:Continuous f): Integrable (fun x=>bowl n r x • f x):= (bowl_cont n r|>.smul h).integrable_of_hasCompactSupport (HasCompactSupport.smul_right (bowl_support n r))

def murmur : poly A →ₗ[ℂ] ℂ where
  toFun p:= pool n r (watches p)
  map_add' p q:= by unfold pool; simp_rw [show ∀ i,watches (p+q) i=watches p i+watches q i from fun i=> map_add ..,smul_add]; exact integral_add (pooling _ _ (watch_kin p).continuous) (pooling _ _ (watch_kin q).continuous)
  map_smul' t p:= by
    unfold pool; simp_rw [show ∀ x,watches (t • p) x=t • watches p x from fun i=> map_smul ..,smul_comm _ t]; rw [integral_smul]; rfl

lemma pool_cycle (i:A)(p:poly A): murmur (n+1) r (pderiv i p)=(2*(↑(n+2:ℕ)) : ℝ) • murmur n r (X i*p):= by
  let φ:VectorA A→ℝ:= bowl (n+1) r; let v:=EuclideanSpace.basisFun A ℝ i
  have hc x:fderiv ℝ (watches p) x v=watches (pderiv i p) x:= spin_eye ..
  have hp x:fderiv ℝ φ x v=(-2*(↑(n+2:ℕ)):ℝ)*bowl n r x *x i:= by rw [(bend_bowl n r x).2 v]; simp [v,EuclideanSpace.inner_single_right]
  let K:ℝ:=2*((n+2:ℕ):ℝ)
  have h x:fderiv ℝ φ x v • watches p x=(-K) • (bowl n r x • watches (X i*p) x):= by rw [hp]; simp [Complex.real_smul, watches,K];ring
  change pool (n+1) r _= _ • pool n r _; unfold pool
  have hU: Integrable (fun x=> fderiv ℝ φ x v • watches p x):= by simp_rw [h]; exact (pooling (A:=A) n r (watch_kin (X i*p)).continuous).smul (-K)
  have hV: Integrable (fun x=> φ x • fderiv ℝ (watches p) x v):= by simp_rw [hc]; exact pooling _ _ (watch_kin _).continuous
  have he:= integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hU hV (pooling _ _ (watch_kin p).continuous) (fun x _=> (bend_bowl n r x).1) (fun x _=> (watch_kin p).differentiable (by simp) x)
  simp_rw [h,hc, integral_smul] at he; simp only [neg_smul,neg_neg] at he; exact he
end
variable {D J:Type*} [Fintype D] [Fintype J] [DecidableEq J]
lemma latent (p:Channel D J) (h:Hide p) (r:ℝ)(u:ℕ): murmur u r p=0:= by
  have he (k:ℕ)(p:Channel D J)(h:Hide p)(hk:p.IsHomogeneous k)(u:ℕ): murmur u r p=0:= by
    induction k using Nat.strong_induction_on generalizing u p with
    | h k ih=>
      by_cases ht:k=0
      · subst k
        have hg := (totalDegree_eq_zero_iff_eq_C).mp (Nat.eq_zero_of_le_zero hk.totalDegree_le)
        have ht:= h.void; rw [hg] at ht
        rw [hg,show coeff 0 p = 0 from (show p.coeff 0=0 from ?_),map_zero,map_zero]
        simpa using ht
      let Z:=∑ i:D×J,pderiv i (pderiv i p)
      have hg : Z.IsHomogeneous (k-1-1):= IsHomogeneous.sum _ _ _ fun i _=>hk.pderiv.pderiv
      have hp:= ih _ (by omega : k-1-1<k) _ (lapHide p h) hg (u+1)
      rw [map_sum] at hp; simp_rw [pool_cycle u r _ _] at hp
      rw [← Finset.smul_sum,← map_sum (murmur u r), hk.sum_X_mul_pderiv, _root_.map_nsmul] at hp
      have hb: k • murmur u r p=0 := (smul_eq_zero.mp hp).resolve_left (by positivity)
      rw [← Nat.cast_smul_eq_nsmul ℝ] at hb; exact (smul_eq_zero.mp hb).resolve_left (by exact_mod_cast ht)
  rw [← p.sum_homogeneousComponent,map_sum]; apply Finset.sum_eq_zero; intro i hi
  have H: Hide (∑ j∈Finset.range (p.totalDegree+1), homogeneousComponent j p):= by rw [sum_homogeneousComponent]; exact h -- direction inspect
  exact he i _ (characteristic _ _ _ (fun i _=> homogeneousComponent_mem ..) H hi) (homogeneousComponent_mem ..) _
end YM.XSpace.Stab
