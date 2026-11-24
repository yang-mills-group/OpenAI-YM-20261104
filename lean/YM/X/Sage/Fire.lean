import YM.X.Sage.Quick
/-!
# tensor formula for β replacement scans. ∗all factor orientation*.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+}{r s e:ℝ}
local notation "U"=> G.ColorIndex
local notation "T"=> Tet
variable (A:Symmetric V)
lemma tri_one : tri A 1 1 1=1:= by rw [tri, Tot.market]; simp
lemma tri_box (x y:ℂ): tri A 1 (MvPolynomial.C x) (MvPolynomial.C y)=x*y:= by
    have he(z:ℂ):C (σ:=V) z=z • 1:=by rw [← C_mul',mul_one]
    rw [he,_root_.YM.PositionX.Tot.tri_scale₁,he y,tri_scale₂,tri_one]; simp
lemma quartet (x y z t:V→₀ℂ): tri A (glyph x*glyph y) (glyph z) (glyph t)= treats A x z * treats A y t + treats A x t * treats A y z:= by rw [tri_cross]; simp_rw [link,chop₁,link]; simp only [edge,slit_C,tri_z₁,tri_z₂,tri_box,add_zero,zero_add]; ring; 
local notation "Q"=> qu q G k
local notation "ε"=> epsilon q k
local notation "N"=> side q k
local notation "K"=> wrap N
local notation "E"=>tri Q
-- numeric quaternion residual Φ
variable (z x y w:Cover)(p t i l:Tet)(a b c:G.ColorIndex)
def fars (q:ℕ+)(k:ℕ)(z x:Cover)(p t:T):ℝ:= Wpp (epsilon q k) 1 p (-1) t (side q k) (wrap _ z) (wrap _ x)
def nearA (q:ℕ+)(k:ℕ)(x w:Cover)(p:T)(i:Axis):ℝ:= Wpv (epsilon q k) (-1) p i (side q k) (wrap _ x) (wrap _ w)
def segmentA (n:Side)(e:ℝ)(z x y:Site n):T→ T→ T→ℝ:= Α (fun i v=>Wpp e 1 i (-1) v n z x) (fun i v=>Wpp e 1 i (-1) v n z y)
local notation "S"=> segmentA N ε (K z) (K x) (K y) -- i-ambiguity
set_option maxHeartbeats 300000 in
lemma pSt (u v:U):
   E (glyph (psiF q k z 1 (loop p) u)*glyph (psiF q k z 1 (Chir.ℓ p) v)) (glyph (psiF q k x (-1) t b)) (glyph (psiF q k y (-1) i c))=
      (if u=b∧v=c then ↑(fars q k z x (loop p) t * fars q k z y (Chir.ℓ p) i) else 0) + (if u=c∧v=b then ↑(fars q k z y (loop p) i*fars q k z x (Chir.ℓ p) t) else 0):= by
     rw [quartet]; simp_rw [ψ_meetPP]; apply congr_arg₂ (·+·) <;> simp only [Complex.ofReal_mul] <;> split_ifs <;> first|rfl|tauto|(exfalso; tauto)|simp
lemma erase₂ (f:U→U→ℂ)(g:ℂ): ∑ u:U,∑ v:U,f u v * (if u=b∧v=c then g else 0) = f b c*g:= by
   rw [Finset.sum_eq_single b]; simp [mul_ite]; intros k ht hk; simp [hk];simp
lemma residue : E (veil z k (restB q p a)) (veil x k (restU q t b)) (veil y k (restU q i c))= ↑(4*ff a b c*segmentA N ε (K z) (K x) (K y) p t i):= by
    unfold restB hook restU; simp_rw [map_sum,map_smul,map_mul,veil_μ,veil_β]; rw [tri_scale₁,tri_scale₂]; simp_rw [tri_sum,tri_scale,pSt]; simp only [smul_eq_mul, mul_add,Finset.sum_add_distrib]; rw [erase₂,erase₂,skew₁ a c b]; unfold segmentA Α fars; push_cast; ring
local notation "H"=> Umark q G
lemma gouge (μ ν:Axis) :
   XEdge q k (psiA q k w μ b) (psiA q k w ν c) (veil z k (restB q p a)) (veil x k (μDeck q G)) (veil y k (μDeck q G)) = ↑(4*ff a b c * ∑ t:T,∑ v:T, nearA q k x w t μ* nearA q k y w v ν * segmentA N ε (K z) (K x) (K y) p t v):= by
    unfold XEdge; rw [←show (Umark q G).seed=μDeck q G from rfl,pickA,pickA]; simp_rw [tri_sum₁,tri_sum₂,tri_scale₁,tri_scale₂, Umark,residue]; push_cast; simp only [smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; unfold nearA; ring
-- total over tensor.Handy.Pl.Identity
lemma plaq_control (M:Axis→Axis→ℝ) (x y:Axis→ℝ)(hk:∀ i j:Axis, M i j=-M j i) : (∑ u:PlaqAxes, M u.val.1 u.val.2 * (x u.val.1*y u.val.2 -x u.val.2*y u.val.1))=∑ i:Axis,∑ j:Axis,M i j * x i * y j := by
    rw [← plaq_turn (fun i j=> M i j*x i*y j) (fun i=>by rw [show M i i=0 from by linarith only [hk i i]]; ring)]; apply Finset.sum_congr rfl; intro i _; rw [hk i.val.2 i.val.1]; ring
-- sign convention ticket caps. 
end YM.PositionX.Sage
