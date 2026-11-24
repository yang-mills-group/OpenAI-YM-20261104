import YM.XSpace.WickLabels

/-!
# The bare Wick-jet prescription

Order matters: the stencil coordinate on leading inputs is algebraic in log-field
coordinates. Use THE FULL infinite-volume massless TOP Wilson covariance to Wick subtract
on these pure field letters (no addresses at top for these inputs). Retain this *same*
linear combination on the higher-order stencil evaluation. This gives `W_(N,d)^{-1}` for this choice of `S_h`. Certify by exactly performing its unmasked W jet test,
before any positioning, on the stencils over the actual offsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Filter Set Lattice RG Wilson Labels Source Source.Drops Finsupp MvPolynomial Top Next.Rank.Normal Contraction
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {H : Hol G} {R : Period} {d : ℕ}
namespace Survey
variable (A : Survey G H d)

def coverTop : Cov (Bean A) := ⟨(fun i j=> bean_kernel A coverLine i j),fun i j=> by
    congr 1; dsimp only [bean_kernel]; split
    next h=> rw [if_pos h.symm, Top.cover_symm _ _ _]; simp only [covariancePosition,neg_sub]
    next h=> rw [if_neg (Ne.symm h)]⟩

def bank (i : Labels.Key G) : Bean A →₀ℂ:= ∑ j:Bean A, single j (bills A (Survey.component i) j:ℂ)
lemma bank_covariance : scope A.bank A.coverTop=A.selfCov 1:=by
  apply Next.Rank.Normal.Symmetric.ext; funext i j; change treats _ (∑ k:Bean A, _) _= ↑((1:ℝ)*bean_cov A coverLine (Survey.component i) (Survey.component j)); rw [one_mul]; unfold bank bean_cov; -- already unfolded bank partially
  rw [treats_sum,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun k _=>?_; rw [treats_comm,treats_sum,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun l _=>?_; rw [treats_comm,treats_single]; simp only [coverTop]; push_cast; ring

def pureColumn := exchange A.bank
lemma column_eval (x : GaugePanel G A.size) (p : Labels.Pol G) : Taylor.evalAt (beanBasis A) x (A.pureColumn p)= read (expand d (A.extract x)) p:=by
  suffices h : (Taylor.evalAt (beanBasis A) x).comp A.pureColumn=read (expand d (A.extract x)) from DFunLike.congr_fun h p
  ext1 i; rw [AlgHom.comp_apply, pureColumn,exchange_x]; dsimp only [bank]; rw [map_sum,map_sum]; simp only [glyph,linearCombination_single,map_smul,Taylor.evalAt, Labels.read,aeval_X, smul_eq_mul]
  have hp : coord (expand d (A.extract x)) i= ↑(Survey.component i (A.extract x)):=rfl
  rw [hp]; conv_rhs=> rw [← (Top.beanBasis A).sum_repr x,map_sum,map_sum]
  push_cast; apply Finset.sum_congr rfl; intro j _; rw [mul_comm,map_smul,map_smul,smul_eq_mul,Complex.ofReal_mul]; rfl

lemma column_jet (x : Snap G d) (p : Labels.Pol G) :
    Taylor.evalAt (beanBasis A) (A.glowing x) (A.pureColumn p) = read (expand d x) p:=by rw [column_eval,A.linear_jet]
/-- certifies the identification of W on this `S_h`. All radial jets tested (globally). -/
lemma wick_jet (J : Jet G) (z : ℝ) (p : Labels.Label G d) :
    Taylor.evalAt (beanBasis A) (A.glowing (trunk d (scaleJet J z))) (milk A.coverTop (A.pureColumn p.val))= read (scaleJet J z) (A.insertW 1 p).val:=by
  unfold pureColumn; rw [prepared,A.bank_covariance,← insertW_val]; exact (A.column_jet ..).trans (racts _ _)
lemma subtraction_exact (p : Labels.Label G d) (J : Jet G) (z : ℝ):
    Taylor.evalAt (beanBasis A) (A.glowing (trunk d (scaleJet J z))) (milk A.coverTop (A.pureColumn (A.insertW (-1) p).val))= read (scaleJet J z) p.val:= by
  rw [A.wick_jet,show A.insertW 1 (A.insertW (-1) p)= _ from neg_neg (1:ℝ) ▸ A.wick_recovers (-1) p]
end Survey

namespace Bare
variable (T : R.Tree) (A : Survey G H d) (x : R.Sites)
def column : Labels.Label G d→ₗ[ℂ] Series T G:= (aeval (factor T A x)).toLinearMap ∘ₗ ((localFields G d).subtype ∘ₗ A.insertW (-1))
theorem column_formula (p : Labels.Label G d) : column T A x p=raw T A x (A.insertW (-1) p).val:=rfl
lemma column_unit : column T A x (unit G d)=1:=by rw [column_formula,A.wick_unit]; exact map_one _

lemma pure_at_zero (p : Labels.Pol G) (v : T.Field G) : Taylor.evalAt (T.basis G) v (PowerSeries.constantCoeff (raw T A x p))=
    Taylor.evalAt (beanBasis A) (fun j=> T.linearCurl v (Work.F03.slotFace (A.looks j) x)) (A.pureColumn p) := by
  rw [A.column_eval]; unfold raw; induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C,PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]; simp [Taylor.evalAt,Labels.read]
  | add p q hp hq=> simp only [map_add,hp,hq]
  | mul_X p i hp=> rw [map_mul,map_mul,map_mul,hp, map_mul,aeval_X,factor_leading,Work.G05.snapCoord_eq]; simp only [Labels.read,aeval_X]

theorem column_uncut (p : Label G d) : A.pureColumn (A.insertW (-1) p).val = milk (-A.coverTop) (A.pureColumn p.val) := by
  rw [Survey.insertW_val,Survey.pureColumn,prepared,scope_neg,A.bank_covariance,A.inverseCov]

lemma factor_parity (i : Labels.Key G): reverseArgs T G (factor T A x i)= -(factor T A x i):=PowerSeries.ext fun n=>by
  rw [reverse_coeff,map_neg (PowerSeries.coeff n),factor,PowerSeries.coeff_mk,Taylor.mirror_divided]; rw [pow_succ, mul_neg_one, neg_mul,mul_neg,← mul_assoc, ← mul_pow,neg_one_mul,neg_neg,one_pow,one_mul]
lemma constant_parity (c : ℂ) : reverseArgs T G (algebraMap ℂ (Series T G) c)= algebraMap ℂ (Series T G) c :=by
  rw [Algebra.algebraMap_eq_smul_one,reverse_scalar,map_one]
lemma reverse_raw (p : Labels.Pol G) : reverseArgs T G (raw T A x p) = raw T A x (Taylor.mirror _ p):=by
  unfold raw; induction p using MvPolynomial.induction_on with
  | C a=> simp only [aeval_C,constant_parity]; simp [Taylor.mirror,MvPolynomial.algebraMap_eq, PowerSeries.algebraMap_apply]
  | add p q hp hq=> simp only [map_add,hp,hq]
  | mul_X p i hp=>rw [map_mul,map_mul,aeval_X,hp,map_mul,map_mul,factor_parity, show Taylor.mirror _ (X i)=-(X i) from aeval_X ..,map_neg (aeval _),aeval_X]
lemma factor_real (i : Labels.Key G): conjugate T G (factor T A x i)=factor T A x i:=PowerSeries.ext fun n =>by
  let f:= labelFunction T A x (X i); have h : f= Complex.ofRealCLM ∘ (Complex.reCLM ∘ f):= funext fun v=>by simp only [f,comp_apply,labelFunction,Labels.read,aeval_X]; rfl
  have he: ContDiffAt ℝ ω (Complex.reCLM ∘ f) 0:=Complex.reCLM.contDiff.contDiffAt.comp _ (label_smooth T A x (X i))
  rw [conjugate,PowerSeries.coeff_map,factor,PowerSeries.coeff_mk]; change Taylor.conjPol _ (Taylor.divided _ (n+1) f)=Taylor.divided _ _ f; rw [h,Taylor.divided_real _ _ _ (he.of_le le_top)]
lemma raw_real (p : Labels.Pol G) : conjugate T G (raw T A x p) = raw T A x (Labels.conjPol p):=by
  unfold raw Labels.conjPol; induction p using MvPolynomial.induction_on with
  | C a=> simp only [aeval_C,MvPolynomial.map_C,PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]; rw [conjugate,PowerSeries.map_C,Taylor.conjPol,MvPolynomial.map_C]
  | add p q hp hq=> simp only [map_add,hp,hq]
  | mul_X p i hp=> rw [map_mul,map_mul,map_mul,map_mul,hp, aeval_X,MvPolynomial.map_X,aeval_X,factor_real]
lemma column_real (p : Label G d) : conjugate T G (column T A x p)=column T A x (realBar p):=by rw [column_formula,column_formula,A.wick_real,raw_real]; rfl
variable {T A x} in
lemma slot_parity (n : ℕ) (p : Labels.Pol G) (h : ∀ i∈ p.support,n=i.sum fun _ a=>a) : Taylor.mirror _ p = ((-1:ℂ)^n) • p:=by
  classical
  rw [p.as_sum,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [monomial_eq,map_mul]; unfold Finsupp.prod; rw [map_prod]; simp only [map_pow,Taylor.mirror,aeval_X,aeval_C, MvPolynomial.algebraMap_eq, show ∀ i:Labels.Key G,-(X i:Labels.Pol G)= -1*X i from fun i=>by simp, mul_pow]; rw [Finset.prod_mul_distrib,h i hi,Finsupp.sum,Finset.prod_pow_eq_pow_sum,← C_mul',map_pow]; simp; ring
lemma column_parity (n : ℕ) {p : Label G d} (h : Taylor.mirror _ p.val= ((-1:ℂ)^n) • p.val) : HasParity T n (column T A x p):=by
  unfold HasParity; rw [column_formula,reverse_raw,Survey.insertW_val, ← Taylor.reflected_milk, h,map_smul]; exact map_smul (aeval _) _ _
end Bare
end YM.XSpace
