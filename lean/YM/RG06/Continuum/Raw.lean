import YM.RG06.Continuum.ConnectionJets
import YM.RG06.Lattice.Words -- same Color basis expansion
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The independent bare 4D local prescriptions on raw continuum jets

All connection/curvature operators in this layer use the countable polynomial algebra of
local ordinary connection jets. Normalize an ordinary derivative of order k WITHOUT k! (so our
`next` prolongation is the usual derivation and never touches explicit position). In covariant
slots normalize explicitly by k! to conform to `Source.Projects`, Maxwell Taylor, etc. Keep every
ordered tensor (do not sort w for D's); later impose relations by evaluation on actual germs, not
by names. Color contractions complexified only in polynomials. The finite dimensional external
evanescent/gauge-variant sector is NOT quotiented by this 4D test.

Stipulation: when using these tree symbols as definitions in a field prescription, use real g=λ
without folding any g from A. At g=1 the continuum-to-Wilson links/log convention matches
our radial reader; equivalently rescale an arbitrary connection B by g then divide once per
curvature. Additional theorem records that equivalence at algebraic level, no physical scheme
identification. There are no ghosts at this 4D curvature-sector tree stage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
namespace Raw
open Analysis Lattice MvPolynomial Tensor
open scoped Topology ContDiff BigOperators Classical ComplexConjugate InnerProductSpace
variable {G : Gauge}
structure Key (G : Gauge) where
  primary: Axis
  chain: List Axis
  color:G.ColorIndex
  deriving DecidableEq
abbrev Pol (G : Gauge) := MvPolynomial (Key G) ℂ
abbrev Vector (G:Gauge):=G.ColorIndex→Pol G

def read (A:Connection G)(x:E4):Pol G→+*ℂ:= MvPolynomial.eval fun i=> ↑(derivative i.chain (A i.primary) x i.color)
lemma read_diff (A:Connection G) (h:Smooth A)(p:Pol G): Good (fun x=> read A x p):=by
  induction p using MvPolynomial.induction_on with
  | C c=> simp_rw [read,eval_C]; exact contDiff_const
  | add p q hp hq=> simpa only [map_add] using! ContDiff.add hp hq -- helper?
  | mul_X p k hp=> simp_rw [_root_.map_mul,read,eval_X]; refine ContDiff.mul hp ?_; exact (Complex.ofRealCLM ∘L EuclideanSpace.proj k.color).contDiff.comp (higher (h _) k.chain)

/-- Prolongation in a partial-derivative slot. This is a derivation on an *ordered* jet book:
partial derivatives commute after evaluation, not asserted by ignoring the order. -/
def extendX (g:Axis)(i: Key G):Pol G:= X ⟨i.primary,g::i.chain,i.color⟩
def extending (g:Axis) : Derivation ℂ (Pol G) (Pol G):= mkDerivation ℂ (extendX g)

lemma differentiated (p: Pol G)(i:Axis)(A:Connection G)(h:Smooth A)(x:E4):
    read A x (extending i p) = par i (fun y=> read A y p) x:= by
  have he(k:Key G):read A x (extending i (X k))=par i (fun y=> read A y (X k)) x:=by
    let L: G.Color→L[ℝ]ℂ:= Complex.ofRealCLM ∘L EuclideanSpace.proj k.color
    have hh:=par_linear L (h:=higher (h k.primary) k.chain) i
    rw [extending,mkDerivation_X]; simp_rw [read,extendX,MvPolynomial.eval_X, derivative]
    exact (congr_fun hh x).symm -- hh derivatives k.chain; derivative unfolds pattern?
  induction p using MvPolynomial.induction_on with
  | C c=>
     have hh:extending (G:=G) i (C c)=0:=by change mkDerivationₗ ℂ _ _ = _; exact mkDerivationₗ_C _ _
     rw [hh,map_zero]; simp [read,par,D]
  | add p q hp hq=>
    rw [map_add,map_add,hp,hq]
    simp only [map_add]; exact (congr_fun (par_add (read_diff A h p) (read_diff A h q) i) x).symm
  | mul_X p k hp=>
    rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,_root_.map_mul,_root_.map_mul,hp,he]; simp only [_root_.map_mul]
    have hu:= (((read_diff A h p).germ x).hasFDerivAt.mul ((read_diff A h (X k)).germ x).hasFDerivAt).fderiv
    unfold par D; erw [hu]; rfl

abbrev paint (G:Gauge)(i:G.ColorIndex):G.Color:= WilsonRules.baseColor G i
/-- Adjoint Lie structure constants, no i (skew-matrix variables). -/
def constant (i j k:G.ColorIndex):ℝ:=G.ad (paint G i) (paint G j) k

def cross (p q:Vector G)(k:G.ColorIndex):Pol G:= ∑ i,∑ j,MvPolynomial.C (↑(constant i j k) : ℂ)*p i*q j

lemma cross_value (p q:Vector G)(A:Connection G)(x:E4)(P Q:G.Color)
   (hp:∀ i,read A x (p i)= ↑(P i))(hQ:∀ i,read A x (q i)= ↑(Q i))(k:G.ColorIndex):
   read A x (cross p q k)=((G.ad P Q k : ℝ) : ℂ) := by
  unfold cross; simp only [_root_.map_sum,_root_.map_mul,hp,hQ]
  simp only [read,eval_C]
  conv_rhs=> rw [← WilsonRules.base_expansion P, ← WilsonRules.base_expansion Q]
  simp only [_root_.map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,PiLp.smul_apply, WithLp.ofLp_sum,Finset.sum_apply,Complex.ofReal_sum,Complex.ofReal_mul,smul_eq_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; unfold constant paint; push_cast; ring

def primitive (i:Axis):Vector G:=fun a=>X ⟨i, [],a⟩
lemma prim_read (i:Axis)(a:G.ColorIndex)(A:Connection G)(x:E4):read A x (primitive i a)= ((A i x a : ℝ) :ℂ):=by simp [read,primitive,derivative]

def kick (i:Axis)(v:Vector G):Vector G:=fun a=>extending i (v a)
def field (g:ℂ)(i j:Axis):Vector G:=
    kick i (primitive j) + -(kick j (primitive i)) + g • cross (primitive i) (primitive j)

def haul (g:ℂ)(i:Axis)(v:Vector G):Vector G:= kick i v + g • cross (primitive i) v

/-- Explicit curvature derivative *polynomial* recursion. -/
def sequence (g:ℂ):{j:ℕ}→(Fin j→ Axis)→Vector G→ Vector G
 | 0,_,v=>v
 | _+1,w,v=>haul g (w 0) (sequence g (Fin.tail w) v)

def frame (g:ℂ){j:ℕ}(w:Fin j→ Axis)(a b:Axis)(k:G.ColorIndex):Pol G:=
   MvPolynomial.C ((j.factorial:ℂ)⁻¹)* sequence g w (field g a b) k

lemma weight_eval (A:Connection G)(x:E4)(p q:Vector G)(r s:Section G)
    (hp:∀ a,read A x (p a)=(↑(r x a):ℂ)) (hs:∀ a,read A x (q a)=(↑(s x a):ℂ))(g:ℝ)(b:G.ColorIndex) :
    read A x (((↑g:ℂ) • cross p q:Vector G) b)=(↑((g • G.ad (r x) (s x):G.Color) b):ℂ):=by
    rw [Pi.smul_apply,MvPolynomial.smul_eq_C_mul,_root_.map_mul,cross_value _ _ _ _ _ _ hp hs,read,eval_C]
    simp

lemma kick_read (A:Connection G)(h:Smooth A)(p:Vector G)(q:Continuum.Section G)(hq:Good q)
    (hp: ∀ x a, read A x (p a)=↑(q x a))(i:Axis)(x:E4)(b:G.ColorIndex):read A x (kick i p b)=↑(par i q x b):=by
  simp_rw [kick,differentiated (A:=A) (h:=h),hp] -- args
  let L:G.Color→L[ℝ]ℂ:= Complex.ofRealCLM ∘L EuclideanSpace.proj b
  change par i (fun x=>L (q x)) x=L _; rw [par_linear L hq i]

lemma grid (A:Connection G)(h:Smooth A)(g:ℝ)(i j:Axis)(x:E4)(b:G.ColorIndex):read A x (field (↑g) i j b)= ↑(curvature g A i j x b):=by
  simp only [field, Pi.add_apply,Pi.neg_apply,_root_.map_add,_root_.map_neg, kick_read A h (primitive i) (A i) (h i) (fun x a=> prim_read _ _ _ _), kick_read A h (primitive j) (A j) (h j) (fun x a=> prim_read _ _ _ _), weight_eval A x _ _ (A i) (A j) (fun _=> prim_read _ _ _ _) (fun _=>prim_read _ _ _ _) g b]
  unfold curvature bracket; simp

lemma dominate (A:Connection G)(h:Smooth A)(g:ℝ)(v:Vector G)(B:Section G)(hb:Good B)
    (hv:∀ x a,read A x (v a)=↑(B x a))(i:Axis)(x:E4)(c:G.ColorIndex):read A x (haul (↑g) i v c)= ↑(covariant g A i B x c):=by
   rw [haul,Pi.add_apply,map_add,kick_read A h v B hb hv,weight_eval A x _ _ (A i) B (fun _=>prim_read _ _ _ _) (hv x) g c]; simp [covariant,bracket]
lemma sequence_eq (A:Connection G)(h:Smooth A)(g:ℝ){j:ℕ}(w:Fin j→Axis) (v:Vector G)(B:Section G)(hb:Good B)
    (hv:∀ x a,read A x (v a)=↑(B x a))(x:E4)(c:G.ColorIndex):read A x (sequence (↑g) w v c)= ↑(nablas g A w B x c):= by
   induction j generalizing x c with
   | zero=>exact hv x c
   | succ j H=> exact dominate A h g (sequence _ (Fin.tail w) v) (nablas g A (Fin.tail w) B) (Smooth.higherCov g A h _ _ hb) (fun x c=>H _ x c) _ x c
lemma frame_eq (A:Connection G)(h:Smooth A)(g:ℝ){j:ℕ}(w:Fin j→Axis)(a b:Axis)(x:E4)(c:G.ColorIndex):read A x (frame (↑g) w a b c)= ↑(covJet g A w a b x c):=by
  unfold frame;rw [_root_.map_mul,sequence_eq A h g _ _ (curvature g A a b) (Smooth.F g A h a b) (grid A h g a b),read,eval_C]; simp only [covJet, PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv, Complex.ofReal_natCast]

end Raw
end YM.RG06.Continuum
