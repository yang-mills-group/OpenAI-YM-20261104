import YM.RG06.Bare.Section
import YM.RG06.Symbol.Language
/-!
# Native site-relative Taylor functional (no adjacencies / coarse masks)

`Kernel G X` -- finite potential polynomial, not redundant covers collapsed
into a regulator torus until reannouncement. The scalar tangent variables
represent REAL components in the given `Gauge.Color`. All are indexed by
incoming positive, starting-site links (from which negative directions read
shifted negatives). Inversions/profiles kept for consumers downstream. This
and next file realize finite polynomial kernels order by order (e uses
1/e! derivatives) for insertion germs, with rank kept BEFORE any measure. No
coupling-reset or cumulant identity assumed: with physical spacing a at
report units an insertion of announced horizon d with own Labels.basis slot
count l is a^-d * g_i^-l * nativeKernel; for application to C.O one
uses `Rules.bareRule` etc instead. Includes nonlinear powers.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.RG06.Tokens
open Function Filter Lattice RG Labels Source
open MvPolynomial hiding C X
open scoped Matrix.Norms.Frobenius BigOperators Topology InnerProductSpace Classical ContDiff
variable {G : Gauge} {X Y:Type}

abbrev Leg (G:Gauge)(X:Type) := Edge (Four X) × G.ColorIndex
abbrev Kernel (G:Gauge)(X:Type) := MvPolynomial (Leg G X) ℂ

def axis (G:Gauge)(i:G.ColorIndex):=EuclideanSpace.basisFun G.ColorIndex ℝ i

def finger (A:Links X G.Color)(l:Leg G X):ℂ:=A l.1 l.2

def applyHere (A:Links X G.Color) : Kernel G X→ₐ[ℂ]ℂ:= aeval (finger A)
@[simp] theorem finger_X (A:Links X G.Color)(l:Leg G X): applyHere A (MvPolynomial.X l)=finger A l:=by simp [applyHere]
@[simp] theorem finger_C (A:Links X G.Color)(c:ℂ):applyHere A (MvPolynomial.C c)=c:=by simp [applyHere]

lemma extReal {α:Type}(p q:MvPolynomial α ℂ)(h:∀ x:α→ℝ,aeval (fun i=> (x i:ℂ)) p=aeval (fun i=>(x i:ℂ)) q): p=q:=by
  classical
  apply funext_set (fun _:α=>Set.range (fun (z:ℕ)=> (z:ℂ))) (fun i:α=>Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  choose n hn using fun i=>hx i (Set.mem_univ _)
  have he : x=fun i:α=>((n i:ℝ):ℂ):=by ext1 i; rw [←hn i]; simp
  rw [he]; exact h (fun i=>(n i:ℝ))

theorem unisolvent (p q:Kernel G X)(h:∀ v,applyHere v p=applyHere v q): p=q:=by
  refine extReal _ _ fun w=>?_
  let V: Links X G.Color:=fun x=> WithLp.toLp 2 (fun i=> w (x,i))
  exact h V

def varnish : Kernel G X→+*Kernel G X := MvPolynomial.map (starRingEnd ℂ)
@[simp] lemma varnish_C (c:ℂ):varnish (MvPolynomial.C c : Kernel G X)=MvPolynomial.C (star c):=MvPolynomial.map_C ..
@[simp] lemma varnish_X(l:Leg G X):varnish (MvPolynomial.X l)=MvPolynomial.X l:=MvPolynomial.map_X ..
lemma siteStar (A:Links X G.Color)(p:Kernel G X) : applyHere A (varnish p)=star (applyHere A p):=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp
  | add p q hu hv=>simp only [_root_.map_add,hu,hv,star_add]
  | mul_X p l hp=>simp only [_root_.map_mul,varnish_X,finger_X,hp,star_mul]; dsimp [finger]; rw [Complex.conj_ofReal,mul_comm]
lemma varnish_twice (p:Kernel G X):varnish (varnish p)=p:=unisolvent _ _ fun x=>by simp [siteStar]

abbrev oneRank {α:Type}: α→ℕ:=fun _=>1
abbrev ranked {α:Type}(p:MvPolynomial α ℂ)(d:ℕ):Prop:=IsWeightedHomogeneous oneRank p d
lemma node_X(l:Leg G X) : ranked (MvPolynomial.X l) 1:=isWeightedHomogeneous_X ℂ oneRank l
lemma varnish_ranked (r:ℕ){p:Kernel G X}(h:ranked p r):ranked (varnish p) r:=
    fun j he=>h (by
      have hv:= MvPolynomial.coeff_map (p:=p) (starRingEnd ℂ) j
      contrapose! he; rw [show varnish p=MvPolynomial.map (starRingEnd ℂ) p from rfl,hv,he,map_zero])
lemma ranked_scale (r:ℕ){p:Kernel G X}(h:ranked p r)(a:ℝ)(v:Links X G.Color):
    applyHere (a • v) p=(a:ℂ)^r * applyHere v p := by
  induction h using IsWeightedHomogeneous.induction_on with
  | zero=> simp only [_root_.map_zero,mul_zero]
  | add p q _ _ hu hv=> simp only [_root_.map_add,hu,hv,mul_add]
  | monomial b c hc=>
    rw [monomial_eq]; unfold Finsupp.prod; simp only [_root_.map_mul,map_pow,map_prod,finger_C,finger_X]
    have he i:finger (a • v) i=(a:ℂ)*finger v i:=Complex.ofReal_mul ..
    simp_rw [he,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]; rw [← hc,Finsupp.weight_apply]; unfold Finsupp.sum; simp only [smul_eq_mul,mul_one,oneRank]; ring

lemma steering (v:Links X G.Color)(x): ∑ i:G.ColorIndex, v x i • axis G i=v x:=by
  have he : ∑ i:G.ColorIndex, (EuclideanSpace.basisFun G.ColorIndex ℝ).repr (v x) i • axis G i=v x:= (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr ..
  simpa using! he

abbrev shape (G:Gauge)(R:Type) := Matrix (Fin G.repDim) (Fin G.repDim) R
private def valueM {R:Type}(c:MvPolynomial (Leg G X) ℂ→R)(m:shape G (Kernel G X)):shape G R:=fun i j=> c (m i j)
lemma matrixTransport {R S:Type}[CommSemiring R][CommSemiring S][Algebra ℂ R][Algebra ℂ S](f:R→ₐ[ℂ]S)(a b:shape G R)(c d): f ((a*b) c d)=((a.map f)*(b.map f)) c d:=by simp_rw [Matrix.mul_apply,map_sum,map_mul,Matrix.map_apply]
lemma powersTransport {R S:Type}[CommSemiring R][CommSemiring S][Algebra ℂ R][Algebra ℂ S](f:R→ₐ[ℂ]S)(a:shape G R)(k:ℕ): (a^k).map f=a.map f ^ k:=by
  induction k with
  | zero=>rw [pow_zero,pow_zero]; ext1 i j; simp [Matrix.one_apply]
  | succ k hk=>rw [pow_succ,pow_succ,←hk]; ext1 i j; exact matrixTransport ..

def emission (G:Gauge)(x : Edge (Four X)) : shape G (Kernel G X) := ∑ i:G.ColorIndex, (G.colorMat (axis G i)).map MvPolynomial.C * (Matrix.scalar (Fin G.repDim) (MvPolynomial.X (x,i)))
lemma emits (G:Gauge)(x:Edge (Four X))(a b): emission G x a b=∑ i:G.ColorIndex, MvPolynomial.C (G.colorMat (axis G i) a b)*MvPolynomial.X (x,i):=by
  rw [emission,Matrix.sum_apply]
  simp
lemma emits_here (A:Links X G.Color)(x:Edge (Four X))(a b):applyHere A (emission G x a b)=G.colorMat (A x) a b:=by
  simp_rw [emits,map_sum,_root_.map_mul,finger_C,finger_X]
  conv_rhs => rw [← steering A x,_root_.map_sum,Matrix.sum_apply]
  apply Finset.sum_congr rfl fun i _=>?_
  rw [map_smul,Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,mul_comm]
  rfl

def emitSeries (G:Gauge)(x:Edge (Four X))(a b:Fin G.repDim):PowerSeries (Kernel G X):=PowerSeries.mk (fun k=> MvPolynomial.C ((k.factorial:ℂ)⁻¹)* (emission G x ^ k) a b)
lemma emit_here (G:Gauge)(x:Edge (Four X))(a b)(A:Links X G.Color)(k):applyHere A (PowerSeries.coeff k (emitSeries G x a b))= Rules.exponential (A x) k a b:=by
  simp only [emitSeries,PowerSeries.coeff_mk,_root_.map_mul,finger_C]
  unfold Rules.exponential
  change _ = ((k.factorial:ℝ)⁻¹) • ((G.colorMat (A x)^k) a b)
  rw [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
  congr 1
  have hv := Matrix.ext_iff.2 (powersTransport (applyHere A) (emission G x) k) a b
  simp only [Matrix.map_apply] at hv
  rw [hv,show (emission G x).map (applyHere A)=G.colorMat (A x) from by ext1 i j; exact emits_here ..]

lemma emit_ranked (G:Gauge)(x:Edge (Four X))(k:ℕ)(a b):ranked (PowerSeries.coeff k (emitSeries G x a b)) k:= by
  simp only [emitSeries,PowerSeries.coeff_mk]
  apply IsWeightedHomogeneous.C_mul
  induction k generalizing a b with
  | zero=> rw [pow_zero, Matrix.one_apply]; split <;> first | exact isWeightedHomogeneous_one ℂ oneRank | exact isWeightedHomogeneous_zero ℂ oneRank _
  | succ k hk=> rw [pow_succ,Matrix.mul_apply]; apply IsWeightedHomogeneous.sum; intro i _; rw [emits]; exact (hk _ _).mul (IsWeightedHomogeneous.sum _ _ _ (fun j _=> (node_X (G:=G) (x,j)).C_mul _))
end YM.RG06.Tokens
