import YM.XSpace.ReflectionCov
import YM.XSpace.Bare
import YM.XSpace.NormalTools

/-!
# The full native bare covariance on top sources

Pre-position normalization, direct and image terms. From the literal common `Q` used
inside the bare computations. Real lattice values (working over complex coefficients later).
No analytical price yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Bare
open Function Lattice Filter Set Exterior Contraction Next.Rank.Normal Finsupp Top Matrix
open scoped Topology BigOperators InnerProductSpace ComplexOrder
variable {R : Period} {G : Gauge} (T : R.Tree)

def reading (x : Forms G R.side) : Module.Dual ℝ (T.Field G):=(innerₗ (Forms G R.side) x) ∘ₗ T.compass
lemma reading_compass (x : Forms G R.side) (u : T.Field G) : reading T x u=inner ℝ x (T.compass u):=rfl

def impression (x : Forms G R.side) (j : T.Key G) : ℝ := reading T x (T.basis G j)
lemma impression_bilinear (u v : T.Field G) : reading T (T.compass u) v=2*T.quadratic G u v:= T.compass_bilinear u v

def flipped (x : Forms G R.side) := (T.basis G).equivFun.symm (T.covariance G *ᵥ impression T x)
lemma repr_flipped (x : Forms G R.side) : (T.basis G).equivFun (flipped T x)= T.covariance G *ᵥ impression T x := LinearEquiv.apply_symm_apply ..
lemma flip_keys (x : Forms G R.side) (j : T.Key G): T.quadratic G (T.basis G j) (flipped T x)=impression T x j:= by
  have hp : T.hessian G *ᵥ (T.basis G).equivFun (flipped T x) = impression T x:=by rw [repr_flipped, Matrix.mulVec_mulVec,T.covariance_val, Matrix.one_mulVec]
  conv_lhs=> rw [← (T.basis G).sum_repr (flipped T x), map_sum]
  rw [← hp]; apply Finset.sum_congr rfl; intro k _; rw [map_smul,smul_eq_mul,mul_comm]; simp [Period.Tree.hessian]
lemma hessian_flip (x : Forms G R.side) (u : T.Field G): T.quadratic G u (flipped T x)=reading T x u:= by
  rw [← (T.basis G).sum_repr u, _root_.map_sum,_root_.map_sum, LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_; rw [_root_.map_smul,_root_.map_smul,LinearMap.smul_apply, flip_keys]; rfl
lemma rhs_projection (x : Forms G R.side): T.compass (flipped T x)=(2:ℝ) • (R.Equivariant G).starProjection x:=by
  let y:=flipped T x
  rw [← map_smul]; symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (T.even_compass y) ?_
  intro w hw
  obtain ⟨u,rfl⟩:=T.compass_onto w hw
  rw [inner_sub_left, T.compass_bilinear,T.symmetric,real_inner_smul_left,hessian_flip, reading_compass,sub_self]

/-- Row in the Wick computation, reusable for every local insertion test. -/
def appeal (x : Forms G R.side) : T.Key G →₀ ℂ:= ∑ j:T.Key G, Finsupp.single j (impression T x j : ℂ)
lemma appeal_eval (x : Forms G R.side) (u : T.Field G): Taylor.evalAt (T.basis G) u (glyph (appeal T x))=↑(reading T x u):=by
  unfold appeal; simp only [map_sum,Taylor.evalAt,glyph,Finsupp.linearCombination_single,map_smul, MvPolynomial.aeval_X]
  conv_rhs => rw [← (T.basis G).sum_repr u,map_sum]; simp only [map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _=> mul_comm ..

lemma actual_cov (x y : Forms G R.side): treats (Q T G) (appeal T x) (appeal T y) = ↑(inner ℝ x ((Curled G R.side).starProjection y+(Curled G R.side).starProjection (R.mirrorFace y))) :=by
  calc _ = ↑(reading T x (flipped T y)) := ?_
       _ = _ := by rw [reading_compass,rhs_projection,R.projection_formula]
  unfold appeal; rw [treats_sum]; conv_rhs => rw [← (T.basis G).sum_repr (flipped T y), map_sum,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _=>?_; rw [treats_comm,treats_sum]
  rw [← Module.Basis.equivFun_apply, _root_.map_smul, smul_eq_mul]
  rw [repr_flipped]; unfold Matrix.mulVec dotProduct; rw [Finset.sum_mul,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _=> ?_; rw [treats_comm,treats_single]; dsimp only [Q, impression]; push_cast; ring

-- convenient positions
abbrev At (R : Period) (G : Gauge) := Faces R.side × G.ColorIndex

def faceAppeal (j : At R G) : T.Key G →₀ ℂ:= appeal T (unitFace j.1 j.2)

def direct {n : Side} (p q : Top.Faces n) (a b : G.ColorIndex) : ℝ:= inner ℝ (unitFace p a) ((Curled G n).starProjection (unitFace q b))
lemma direct_symm {n : Side} (p q : Top.Faces n) (a b : G.ColorIndex) : direct p q a b=direct q p b a:=by rw [direct,direct, ← Submodule.inner_starProjection_left_eq_right,real_inner_comm]
lemma direct_at {n : Side} (p q : Top.Faces n) (a b : G.ColorIndex) : direct p q a b=if a=b then projector n (faces n p) (faces n q) else 0:=by unfold direct; rw [atFace,projects_unit]
lemma direct_lattice {n : Side} (p q : Top.Faces n) (a b : G.ColorIndex) {x : Cover} (h : wrap n x=p.1-q.1) : direct p q a b=if a=b then (fourier n p.2 q.2 x).re else 0:=by
  have ht:= spectral p q a b h; split
  next H=> rw [if_pos H] at ht; exact congr_arg Complex.re ht
  next H=> rw [if_neg H] at ht; exact Complex.ofReal_eq_zero.mp ht

def image {R : Period} (p q : Faces R.side) (a b : G.ColorIndex) := direct p (R.reflectedFace q) a b
lemma image_symm (p q : Faces R.side) (a b : G.ColorIndex) : image (R:=R) p q a b=image (R:=R) q p b a := by
  unfold image; rw [direct_symm q,direct,direct, ← R.mirror_at_face, ← R.mirror_at_face, R.symmetric, R.mirror_star]
lemma orbit_pairs (p q : At R G): treats (Q T G) (faceAppeal T p) (faceAppeal T q) = (direct p.1 q.1 p.2 q.2 + image (R:=R) p.1 q.1 p.2 q.2:ℝ):=by
  unfold faceAppeal; rw [actual_cov,R.mirror_at_face,inner_add_right]; rfl

lemma measures_face (p : At R G) (u : T.Field G): Taylor.evalAt (T.basis G) u (glyph (faceAppeal T p))= ↑(T.linearCurl u p.1 p.2):=by rw [faceAppeal,appeal_eval,reading_compass,atFace,T.compass_at]
end YM.XSpace.Bare
