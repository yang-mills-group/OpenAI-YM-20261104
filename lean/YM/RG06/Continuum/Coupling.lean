import YM.RG06.Continuum.RadialQuot
import YM.RG06.Lattice.Weights
 import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Coupling and slot count of the independent curvature prescription

`series` substitutes an explicit coefficient for every glyph. Keep layers tagged by engineering
weight plus curvature slot degree; output rank on raw jets is exactly that degree plus coupling
order (no 1/g loss in symbolic perturbation). `corresponds` evaluates finite series on bare
continuum germs where the conditional Gaussian or Wick / subtraction are not involved (pure
polynomial vertex identity, not existence of interactions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open MvPolynomial Function
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Form
variable {G:Gauge}

def rule (p:Glyph G):PowerSeries (Raw.Pol G):= PowerSeries.mk (Raw.coeffFrame p.chain p.faceL p.faceR p.color)
def series :Form.Pol G→+*PowerSeries (Raw.Pol G):= eval₂Hom (PowerSeries.C.comp MvPolynomial.C) rule

def valid (m:ℕ × ℕ)(p:PowerSeries (Raw.Pol G)):=∀k,Tier Raw.measure (m.1,m.2+k) (PowerSeries.coeff k p)
lemma ruled (p:Glyph G):valid (weight p,1) (rule p):=by
  intro k; rw [rule,PowerSeries.coeff_mk,Nat.add_comm]; exact Raw.grade_frame p.chain _ _ _ _
namespace V
variable {m n:ℕ×ℕ}{p q:PowerSeries (Raw.Pol G)}
lemma constant (v:ℂ): valid (0,0) (PowerSeries.C (MvPolynomial.C v) :PowerSeries (Raw.Pol G)):=by
  intro k; rw [PowerSeries.coeff_C];split
  next h=> subst k; exact MvPolynomial.isWeightedHomogeneous_C ..
  exact isWeightedHomogeneous_zero ..
lemma add (h:valid m p)(hp:valid m q):valid m (p+q):= by intro k; rw [map_add]; exact (h k).add (hp k)
lemma product (h:valid m p)(hp:valid n q):valid (m+n) (p*q):=by
  intro k; rw [PowerSeries.coeff_mul]; apply MvPolynomial.IsWeightedHomogeneous.sum; intro a ha;
  have ht:= Finset.mem_antidiagonal.mp ha
  rw [show ((m+n).1,(m+n).2+k)=(m.1,m.2+a.1)+(n.1,n.2+a.2) from Prod.ext rfl (by dsimp;omega)]; exact (h _).mul (hp _)
lemma powers (h:valid m p)(r:ℕ): valid (r • m) (p^r):= by
  induction r with
  | zero=> rw [pow_zero,zero_smul, show (1:PowerSeries (Raw.Pol G))= PowerSeries.C (MvPolynomial.C 1) by simp]; exact constant _
  | succ r H=> rw [add_smul,one_smul, pow_succ]; exact product H h
lemma all {I : Type*} (s:Finset I)(p:I→PowerSeries (Raw.Pol G))(f:I→ℕ×ℕ)(h:∀i∈s,valid (f i) (p i)):valid (∑ i∈s,f i) (∏i∈s,p i):=by
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty,Finset.prod_empty,show (1:PowerSeries (Raw.Pol G))= PowerSeries.C (MvPolynomial.C 1) by simp]; exact constant _
  | insert a s ha H=> rw [Finset.sum_insert ha,Finset.prod_insert ha]; exact product (h _ (Finset.mem_insert_self ..)) (H (fun _ hi=>h _ (Finset.mem_insert_of_mem hi)))
end V

theorem completeSymbol (p:Form.Pol G)(m : ℕ × ℕ)(h:Tier Form.bidegree m p):valid m (series p):=by
  rw [p.as_sum,map_sum]
  intro k; rw [map_sum]; apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b hb
  have H:=h (MvPolynomial.mem_support_iff.mp hb)
  unfold series; rw [eval₂Hom_monomial, RingHom.comp_apply];
  have he:0+(∑ i∈b.support,b i • bidegree i)=m:=by simpa only [zero_add,Finsupp.weight_apply,Finsupp.sum] using H
  rw [← he]; exact V.product (m:=(0:ℕ × ℕ)) (V.constant _) (V.all b.support (fun i=> rule i ^ b i) (fun i=> b i • bidegree i) (fun i _=>V.powers (ruled i) _)) k

/-- Coupling spine is a genuine polynomial before Wick/Laurent subtractions. -/
def tree (p: Glyph G) : Polynomial (Raw.Pol G):=
   ∑ k∈Finset.range (p.order+2), Polynomial.monomial k (PowerSeries.coeff k (rule p))

def trunk : Form.Pol G→+* Polynomial (Raw.Pol G):= eval₂Hom (Polynomial.C.comp MvPolynomial.C) tree

lemma tree_coe (p:Glyph G) : ((tree p : Polynomial (Raw.Pol G)):PowerSeries (Raw.Pol G))=rule p:=by
  apply PowerSeries.ext
  intro k
  change PowerSeries.coeff k (Polynomial.coeToPowerSeries.ringHom (tree p)) = _
  unfold tree;rw [map_sum,map_sum]
  by_cases hk:k∈Finset.range (p.order+2)
  · rw [Finset.sum_eq_single_of_mem k hk]
    · simp
    intro b _ hb; simp [PowerSeries.coeff_monomial,Ne.symm hb]
  rw [Finset.sum_eq_zero (by
    intro a ha
    have hb:a≠k:=by rintro rfl; contradiction
    simp [PowerSeries.coeff_monomial,Ne.symm hb]),rule,PowerSeries.coeff_mk, Raw.coeffFrame,Raw.stops p.chain p.faceL p.faceR k (le_of_not_gt <| mt Finset.mem_range.mpr hk)]; simp

lemma spine_receipt (p:Form.Pol G): (↑(trunk p) : PowerSeries (Raw.Pol G))=series p:=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [trunk,series]
  | add p q hp hq=>rw [_root_.map_add,_root_.map_add,Polynomial.coe_add,hp,hq]
  | mul_X p i hp=>rw [_root_.map_mul,_root_.map_mul,Polynomial.coe_mul,hp]
                    ; simp [trunk,series,tree_coe] -- expected?

lemma tree_eval (g:ℂ)(p:Glyph G): Polynomial.eval (MvPolynomial.C g) (tree p)=encode g p:=by
  unfold tree encode
  rw [Polynomial.eval_finsetSum,Raw.coeff_rebuild g p.chain p.faceL p.faceR p.color (p.order+1) le_rfl]
  apply Finset.sum_congr rfl; intro a _
  simp [rule,Polynomial.eval_monomial,MvPolynomial.smul_eq_C_mul,mul_comm]

lemma trunk_eval (g:ℂ)(p:Form.Pol G): Polynomial.evalRingHom (MvPolynomial.C g : Raw.Pol G) (trunk p)=graph g p:=by
  induction p using MvPolynomial.induction_on with
  | C c=> simp [graph,trunk,Polynomial.coe_evalRingHom]
  | add p q hp hq=> rw [_root_.map_add,_root_.map_add,_root_.map_add,hp,hq]
  | mul_X p i hp=> rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp]
                   ; simp [graph,trunk,Polynomial.coe_evalRingHom,tree_eval]

/-- Number of potential legs never exceeds engineering grade. -/
lemma maxRank (b: Raw.Key G →₀ ℕ): ((Finsupp.weight Raw.measure) b).2 ≤ ((Finsupp.weight Raw.measure) b).1:=by
  simp only [Finsupp.weight_apply,Finsupp.sum,Raw.measure,Prod.snd_sum,Prod.smul_snd,Prod.fst_sum,Prod.smul_fst]
  exact Finset.sum_le_sum fun i _=> smul_le_smul_of_nonneg_left (show 1 ≤ Raw.size i from Nat.le_add_left ..) (Nat.zero_le _)

lemma last_branch {p:Form.Pol G}{n l:ℕ}(h:Tier Form.bidegree (n,l) p){k:ℕ}(hk:n< l+k): (PowerSeries.coeff k (series p))=0:=by
  by_contra hh
  obtain ⟨b,hb⟩:=MvPolynomial.support_nonempty.mpr hh
  have he:=completeSymbol p _ h k (MvPolynomial.mem_support_iff.mp hb)
  have hc:= maxRank b; rw [he] at hc; exact lt_irrefl n (lt_of_lt_of_le hk hc)

lemma tree_degree {p:Form.Pol G}{n l:ℕ}(h:Tier Form.bidegree (n,l) p): (trunk p).natDegree ≤ n-l:= by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb; rw [← Polynomial.coeff_coe,spine_receipt]; exact last_branch h (by omega)

/-- Stipulated independent series rebuilt at any coupling and arbitrary finite horizon. -/
theorem corresponds (p:Form.Pol G){n l:ℕ}(h:Tier Form.bidegree (n,l) p)(g:ℂ){R:ℕ}(hR:n-l ≤ R):
    graph g p= ∑ k∈Finset.range (R+1), g^k • PowerSeries.coeff k (series p):=by
   rw [← trunk_eval,Polynomial.coe_evalRingHom,Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (tree_degree h) (Nat.lt_succ_of_le hR))]
   refine Finset.sum_congr rfl fun i _=>?_ ; rw [← spine_receipt, MvPolynomial.smul_eq_C_mul, Polynomial.coeff_coe]; simp [mul_comm]

/-- Every k-layer radial image lies in a DIFFERENT common slot bigrade (prior to EOM) -/
def layer (k:ℕ)(p:Form.Pol G): YM.Labels.Pol G:= Raw.radialPol (PowerSeries.coeff k (series p))
lemma common_layer {p:Form.Pol G}{n l:ℕ}(h:Tier Form.bidegree (n,l) p)(k:ℕ) :
    Tier YM.Labels.bidegree (n,l+k) (layer k p):= Raw.graded_pol (completeSymbol p _ h k)

lemma layered {p:Form.Pol G}{n l:ℕ}(h:Tier Form.bidegree (n,l) p)(g:ℂ){R:ℕ}(hR:n-l ≤ R):
  toCommon g p= ∑ k∈Finset.range (R+1), g^k • layer k p := by
  change Raw.radialPol _ = _; rw [corresponds p h g hR,map_sum]; refine Finset.sum_congr rfl fun k _=>?_ ; rw [MvPolynomial.smul_eq_C_mul,_root_.map_mul,MvPolynomial.smul_eq_C_mul,Raw.radialPol,MvPolynomial.eval₂Hom_C];rfl

/-- Reconstruction has no further nonlinear *radial* correction. The independent continuum
rule has every nonlinear coefficient, but radial images on the canonical lifts vanish *exactly*,
not just with a bound up to order. -/
lemma forced_rule {d:ℕ}(p: Labels.Label G d){n l:ℕ}(h:p∈Labels.Grade (n,l))(k:ℕ):
    layer k (asGlyph p).val= if k=0 then p.val else 0:=by
  let A:= (asGlyph p).val
  have H: Tier bidegree (n,l) A:= homogeneous p _ h
  by_cases hk:n-l < k
  · unfold layer; rw [last_branch H (by omega),if_neg (show k≠0 by omega),map_zero]
  have he:= layered H (1:ℂ) (R:=n-l) le_rfl
  simp_rw [one_pow,one_smul] at he
  rw [show toCommon 1 A=p.val by exact rebound p (g:=1)] at he
  -- Different layers distinct; in the seed project `piece`.
  let D:=Labels.piece (G:=G) (n,l+k)
  have take: D (∑ i∈Finset.range (n-l+1),layer i A)=layer k A:=by
    rw [map_sum,Finset.sum_eq_single_of_mem k (by simp; omega)]
    exact (common_layer H k).weightedHomogeneousComponent_same
    intro i _ hi; exact (common_layer H i).weightedHomogeneousComponent_ne _ (by simp; omega)
  rw [← take,← he]; split
  next hv=> subst k; exact (Labels.pure_grade (n,l) p|>.mp h).weightedHomogeneousComponent_same
  next hv=> exact (Labels.pure_grade _ p|>.mp h).weightedHomogeneousComponent_ne _ (by simp; omega)

end Form

 variable {G:Gauge}
namespace Raw
/-- Rescale each potential derivative particle by g, constants held. -/
def reset (g:ℂ): Raw.Pol G→ₐ[ℂ] Raw.Pol G:= MvPolynomial.aeval (fun i=> X i * C g)
lemma reset_grade (g:ℂ){n l:ℕ}{p:Raw.Pol G}(h:Tier Raw.measure (n,l) p):reset g p=g^l • p:=by
  change eval₂Hom (algebraMap _ _) (fun i : Key G=> _ * C g) p = _
  rw [Germ.eval₂_monomialScale (X : Key G→Raw.Pol G) (C g) _ p l]
  · simp [MvPolynomial.smul_eq_C_mul,mul_comm]
  intro b hb; have he:=congrArg Prod.snd (h (MvPolynomial.mem_support_iff.mp hb))
  simpa [Finsupp.weight_apply,measure,Finsupp.sum,Prod.snd_sum] using! he

/-- A = g B, tree symbols with covariant bracket and without g respectively, no assumption g≠0. -/
lemma reset_diff (g:ℂ){p: Form.Pol G}{n l:ℕ}(h:Tier Form.bidegree (n,l) p):
    reset g (Form.graph 1 p)=g^l • Form.graph g p:=by
   rw [Form.corresponds p h 1 (R:=n-l) le_rfl,Form.corresponds p h g (R:=n-l) le_rfl,map_sum,Finset.smul_sum]
   refine Finset.sum_congr rfl fun k _=>?_ ; rw [one_pow,one_smul,reset_grade g (Form.completeSymbol p _ h k),smul_smul]; exact congrArg (· • _) (pow_add ..)

lemma scale (A:Connection G)(g:ℝ)(h:Smooth A)(w:List Axis)(a:Axis)(x:E4):
   derivative w ((g • A) a) x = g • derivative w (A a) x:=by
  induction w generalizing x with
  | nil=>exact rfl
  | cons b w H=> rw [derivative,funext H,derivative];exact congr_fun (par_scale g (higher (h a) w) b) x
lemma reset_read (A:Connection G)(g:ℝ)(h:Smooth A)(p:Raw.Pol G)(x:E4):read A x (reset (↑g) p)=read (g • A) x p:=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [read,reset]
  | add p q hp hq=> rw [_root_.map_add,_root_.map_add,_root_.map_add,hp,hq]
  | mul_X p i hp=> rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp]; simp only [reset,aeval_X,_root_.map_mul,read,eval_X,eval_C,scale A g h]; simp [mul_comm]
end Raw
section
open Form
lemma expansion_reset (p:Form.Pol G){n l:ℕ}(h:Tier Form.bidegree (n,l) p)(g:ℝ)(A:Connection G)(s:Smooth A)(x:E4):
   Form.actual 1 (g • A) x p = (↑g:ℂ)^l * Form.actual g A x p:=by
   have hs:Smooth (g • A):=fun i=>ContDiff.const_smul g (s i)
   rw [← Form.tree_receipt p 1 (g • A) hs, Complex.ofReal_one, ← Raw.reset_read A g s, Raw.reset_diff _ h, MvPolynomial.smul_eq_C_mul,_root_.map_mul,Form.tree_receipt p g A s]
   simp [Raw.read]
end
end YM.RG06.Continuum
