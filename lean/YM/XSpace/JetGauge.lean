import YM.XSpace.LapCon

/-!
# Changing Gaussian at cubic Ward order

There is no curvature-antiderivative estimate needed for proof in this file. Change free
covariance within the inverse-Hessian fiber on the horizontal block. Actually need
conditions on the cross-guidance terms (no color coupling). Prove invariance on Ward
polynomials tested underneath a whole product. Needed in using gauge-independent arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.JetGauge
open Filter Set Function Legs Lap MvPolynomial Next.Rank.Normal
open scoped Topology BigOperators Classical
variable {ι J : Type*} [Fintype ι]
abbrev Cov (ι : Type*) := Next.Rank.Normal.Symmetric ι
abbrev δ (i : ι):= slit (choose_var i 1)
lemma full (p : poly ι) : p ∈ Lap.scope Finset.univ:=by unfold Lap.scope; apply MvPolynomial.mem_supported.mpr; simp
lemma whole (p : poly ι) (f : ι→ℂ) : slit f p=∑ i, f i • δ i p:= split_sum f Finset.univ (full p)
abbrev E (M : Cov ι) := blend M 0
def scale (t:ℂ) (V:Cov ι): Cov ι:= ⟨t • V.cov,fun i j=> by simp [V.symm i j]⟩
omit [Fintype ι] in
lemma scale_op (U:Finset ι) (t:ℂ) (V:Cov ι): op U (scale t V)= t • op U V:= LinearMap.ext fun p=> by
  rw [LinearMap.smul_apply,op_at,op_at,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> slit_smul (V.cov i) t _
omit [Fintype ι] in
lemma scale_pow (U:Finset ι) (t:ℂ) (V:Cov ι) (n:ℕ) (p:poly ι): (op U (scale t V)^n) p=t^n • ((op U V^n) p):=by rw [scale_op, smul_pow, LinearMap.smul_apply]

def interpolated (V Y:Cov ι) (x:ℂ): Cov ι:= V+scale x (Y + -V)
omit [Fintype ι] in
lemma plot_formula (V Y:Cov ι) (x:ℂ) (i j:ι): (interpolated V Y x).cov i j=(1-x)*V.cov i j+x*Y.cov i j:=by change V.cov i j+x * (Y.cov i j+ -V.cov i j)=_; ring
omit [Fintype ι] in
lemma plot_self (V Y:Cov ι): interpolated V Y 0=V:= Next.Rank.Normal.Symmetric.ext (funext fun i=> funext fun j=> by rw [plot_formula]; ring)
omit [Fintype ι] in
lemma plot_other (V Y:Cov ι): interpolated V Y 1=Y:= Next.Rank.Normal.Symmetric.ext (funext fun i=> funext fun j=> by rw [plot_formula]; ring)
omit [Fintype ι] in
lemma plot_heat (V Y:Cov ι) (z x:ℂ) (p:poly ι) : E (interpolated V Y x) (milk (scale (z-x) (Y + - V)) p)= E (interpolated V Y z) p:=by
  have h : interpolated V Y x+scale (z-x) (Y + - V)=interpolated V Y z:=by apply Next.Rank.Normal.Symmetric.ext; funext i j; change (interpolated V Y x).cov i j+(z-x)*(Y.cov i j+ -V.cov i j)=_; rw [plot_formula,plot_formula]; ring
  rw [E,E,blend_components,warms,h]; rfl
lemma derivative (p : poly ι) (V Y: Cov ι) (x:ℂ): HasDerivAt (fun t:ℂ=> E (interpolated V Y t) p) ((2:ℂ)⁻¹ * E (interpolated V Y x) (op Finset.univ (Y + -V) p)) x:=by
  let U:Finset ι:= Finset.univ
  let B:= op U (Y + -V); let M:= E (interpolated V Y x)
  obtain ⟨k,hk⟩:= eventually_atTop.mp (thaws U (full p))
  let f (i:ℕ)(t:ℂ):= wgt i*((t-x)^i*M ((B^i) p)); let d(i:ℕ):= wgt i * (((i:ℂ)*(x-x)^(i-1))* M ((B^i) p))
  have hi (t:ℂ): E (interpolated V Y t) p=∑ i∈Finset.range (k+2), f i t:= by
    rw [← plot_heat V Y t x p, ← hk (k+2) (by omega), heat_value,map_sum]; simp_rw [scale_pow,map_smul]; rfl
  have hh (i:ℕ): HasDerivAt (f i) (d i) x:=by unfold f d; convert! (((hasDerivAt_id' x).sub_const x).pow i |>.mul_const _).const_mul _ using 1; ring
  simp_rw [hi]
  rw [show (2:ℂ)⁻¹ * _=(∑ i∈Finset.range (k+2), d i) from Eq.symm ?_]; swap
  · rw [Finset.sum_eq_single_of_mem 1 (by simp)]; dsimp only [d,wgt]; simp [M,B,U]
    intro i _ e; unfold d; by_cases h:i=0; simp [h]; simp [show i-1≠ 0 by omega]
  exact HasDerivAt.fun_sum fun i (_: i∈Finset.range (k+2))=> hh i

-- Prescribe structural constants on this adapted tangent. `main` horizontal
-- indices. H positive in applications. Only require fiber property in proof:
-- K.C acts as identity on horizontal polynomial letters throughout interpolation.
structure Setup (ι J: Type*) [Fintype ι] where
  main : Finset ι
  k : Cov ι
  grade : ι→J
  radical : ∀ i, i ∉ main → ∀ j, k.cov i j=0
  mono : ∀ i j, grade i≠grade j → k.cov i j=0
namespace Setup
variable (D : Setup ι J)
structure Fit (M : Cov ι) : Prop where
  mono : ∀ i j,D.grade i≠D.grade j → M.cov i j=0
  inv : ∀ i, ∀ j∈ D.main,(∑ s:ι, D.k.cov i s*M.cov s j)=choose_var i 1 j
lemma Fit.joins {V Y:Cov ι} (p: D.Fit V) (q:D.Fit Y) (t : ℂ): D.Fit (interpolated V Y t):=by
  constructor
  · intro i j h; rw [plot_formula,p.mono i j h,q.mono i j h]; ring
  intro i j hj; simp_rw [plot_formula,mul_add]; simp_rw [mul_left_comm (D.k.cov i _),Finset.sum_add_distrib, ← Finset.mul_sum]; rw [p.inv i j hj,q.inv i j hj]; ring
lemma Fit.unique {V Y:Cov ι} (p: D.Fit V) (q:D.Fit Y) (i:ι) (hi:i∈D.main) (j:ι) (hj:j∈D.main): V.cov i j=Y.cov i j:=by
  have h (M:Cov ι) (f:D.Fit M) (g:ι →ℂ) (k:ι) (hk:k∈D.main) : (∑ s:ι,g s * ∑ u:ι,D.k.cov s u*M.cov u k)=g k :=by simp_rw [f.inv _ k hk]; simp [choose_var,Pi.single_apply,mul_ite]
  rw [← h Y q (V.cov i) j hj,Y.symm, ← h V p (Y.cov j) i hi]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rw [V.symm i,D.k.symm,Y.symm j]; ring

-- First-order gauge motion: each vertical direction acts one degree later as a linear
-- shift whose generator lives in other colors. `b x i j` sends INPUT j to OUTPUT i.
structure Turn where
  b : ι→ι→ι→ℂ
  mono : ∀ x i j,D.grade i=D.grade j → b x i j=0
  born : ∀ x i j, D.grade x=D.grade j → b x i j=0
  exit : ∀ x i j, D.grade x=D.grade i → b x i j=0

def block (k: ι→ℂ): poly ι := ∑ i:ι, k i • X i
lemma hit (k:ι→ℂ) (i:ι): δ i (block k)=C (k i):=by
  rw [block,map_sum]; simp_rw [(δ i).map_smul,δ,slit_X]
  rw [Finset.sum_eq_single i]; rw [chosen_eq,map_one,← MvPolynomial.C_mul',mul_one]
  · intro j _ hj; rw [chosen_ne hj,map_zero,smul_zero]
  simp
variable (R : D.Turn)
def shift (x i:ι):= block (R.b x i)
def row (i:ι):= block (D.k.cov i)
omit [Fintype ι] in
lemma chooseSymm (i j:ι): choose_var i 1 j=choose_var j 1 i:=by simp [choose_var,Pi.single_apply,eq_comm (a:=j)]
lemma shift_d (x i j:ι): δ j (shift D R x i)=C (R.b x i j):= hit _ _
lemma row_d (i j:ι): δ j (D.row i)=C (D.k.cov i j):= hit _ _

def Centered (p : poly ι): Prop:= ∀ i:ι,i∉D.main → δ i p=0
lemma centered_slit {p:poly ι} (h:D.Centered p) (i:ι): D.Centered (δ i p) := fun j hj=> by rw [δ,δ,slit_slit,show slit (choose_var j 1) p=0 from h j hj,map_zero]

/-- Ward as a condition on the TOTAL ν integrand incl interaction & all corrections. -/
structure Room (p v:poly ι): Prop where
  bill : D.Centered p
  condition : ∀ j,j∉D.main → δ j v= ∑ i:ι,shift D R j i * (D.row i*p - δ i p)
lemma derivative_same (x i j : ι) (p : poly ι) (h : D.grade x=D.grade j): δ j (shift D R x i*(D.row i*p-δ i p)) = shift D R x i * (D.row i*δ j p-δ i (δ j p)):=by
  have hp (v w) : δ j (v*w)=δ j v*w+v*δ j w:= split_leibniz _ _ _
  rw [hp,shift_d,R.born x i j h,map_zero,zero_mul,zero_add,map_sub,hp,row_d,δ,δ,slit_slit (choose_var i 1)]
  by_cases he : D.grade i=D.grade j
  · rw [show shift D R x i=0 from ?_]; simp
    unfold shift block; simp_rw [R.exit x i _ (h.trans he.symm),zero_smul,Finset.sum_const_zero]
  rw [D.mono i j he,map_zero,zero_mul,zero_add]

lemma e_ibp (k:ι→ℂ) (M:Cov ι) (p:poly ι): E M (block k*p)=∑ j:ι,(∑ i:ι,k i * M.cov i j)*E M (δ j p):=by
  rw [block,Finset.sum_mul,map_sum]; simp_rw [smul_mul_assoc,_root_.map_smul,smul_eq_mul, E,blended,Pi.zero_apply,zero_mul, zero_add]
  simp_rw [whole p (M.cov _),map_sum,map_smul, smul_eq_mul,Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]; simp only [mul_assoc]
lemma firewall (M:Cov ι) (h:D.Fit M) (p:poly ι) (he:D.Centered p) (x i:ι): E M (shift D R x i*(D.row i*p-δ i p))=0:=by
  rw [_root_.mul_sub,mul_left_comm,map_sub,sub_eq_zero,row,e_ibp]
  have hp (j:ι): δ j (shift D R x i * p)=C (R.b x i j)*p+shift D R x i*δ j p:= by rw [δ,split_leibniz]; rw [show slit _ (shift D R _ _) = _ from shift_d ..]
  simp_rw [hp, MvPolynomial.C_mul',map_add,map_smul, smul_eq_mul,mul_add]; rw [Finset.sum_add_distrib]
  have hh : (∑ j:ι, (∑ k:ι, D.k.cov i k * M.cov k j) * (R.b x i j * E M p))=0:=by
    apply Finset.sum_eq_zero; intro j _; by_cases hx:D.grade i=D.grade j; rw [R.mono x i j hx]; ring
    rw [Finset.sum_eq_zero,zero_mul]; intro k _; by_cases hh:D.grade i=D.grade k; rw [h.mono k j (by rwa [hh] at hx),mul_zero]; rw [D.mono i k hh,zero_mul]
  rw [hh,zero_add, Finset.sum_eq_single i]
  · by_cases hp:i∈D.main; rw [h.inv i i hp, chosen_eq,one_mul]; simp [he i hp]
  · intro j _ hx; by_cases hp:j∈D.main; rw [h.inv i j hp,chosen_ne hx,zero_mul]; simp [he j hp]
  simp
lemma erased {p v:poly ι} (h: D.Room R p v) (M:Cov ι) (he:D.Fit M) (i:ι) (hi:i∉D.main) (j:ι) (hj:D.grade i=D.grade j): E M (δ j (δ i v))=0:=by
  rw [h.condition i hi,map_sum,map_sum]; apply Finset.sum_eq_zero; intro k _; rw [D.derivative_same R i k j p hj, D.firewall R M he _ (D.centered_slit h.bill j)]
theorem invariant {p v:poly ι} (h: D.Room R p v) (V Y:Cov ι) (f : D.Fit V) (g:D.Fit Y) : E V v= E Y v:=by
  have hx (t:ℂ): HasDerivAt (fun t:ℂ=> E (interpolated V Y t) v) 0 t:=by
    let K:=interpolated V Y t
    suffices H : E K (op Finset.univ (Y + -V) v)=0 by simpa [show E (interpolated V Y t) (op Finset.univ (Y + -V) v)=0 from H] using derivative v V Y t
    have hk : D.Fit K := f.joins _ g t
    rw [op_at,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [whole _ ((Y + -V).cov i),map_sum]; apply Finset.sum_eq_zero; intro j _; change E K ((Y.cov i j + -V.cov i j) • δ j (δ i v))=_; rw [map_smul]
    by_cases h1 : D.grade i=D.grade j
    · by_cases h2:i∈ D.main
      · by_cases h3:j∈ D.main
        · rw [Fit.unique D f g i h2 j h3, add_neg_cancel,zero_smul]
        rw [δ,δ,slit_slit (choose_var i 1),D.erased R h K hk j h3 i h1.symm,smul_zero]
      rw [D.erased R h K hk i h2 j h1,smul_zero]
    rw [f.mono i j h1,g.mono i j h1]; simp
  simpa only [plot_self,plot_other] using is_const_of_deriv_eq_zero (fun t=> (hx t).differentiableAt) (fun t=>(hx t).deriv) 0 1
end Setup
end YM.XSpace.JetGauge
