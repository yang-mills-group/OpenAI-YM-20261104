import YM.X.Sage.Fire
/-!
# determinant tensor weight for θ at a point. paired unit strands; unnormalized. scales across replicas.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ}{V I:Type*} {q:ℕ+}{r s e:ℝ}
local notation "U"=> G.ColorIndex
local notation "T"=>Tet
local notation "o"=> side q k
local notation "K"=> wrap o
local notation "ε"=>epsilon q k
local notation "Q"=>qu q G k
variable (Z X Y:Fielding.Walk)(z x y w:Cover)(p i u v:Tet)(a b c:G.ColorIndex)
local notation "β"=> veil z k (restB q p a)
local notation "μx"=> veil x k (μDeck q G)
local notation "μy"=> veil y k (μDeck q G)
local notation "A"=> segmentA o ε (K z) (K x) (K y)
def feeV (q:ℕ+)(k:ℕ)(z x y w:Cover)(p:Tet)(ι ψ:Axis):ℝ:=∑ t:T,∑ v:T, nearA q k x w t ι* nearA q k y w v ψ * segmentA (side q k) (epsilon q k) (wrap _ z) (wrap _ x) (wrap _ y) p t v
def groupκ (q:ℕ+)(k:ℕ)(z x y w:Cover)(p:Tet)(D:PlaqAxes):= feeV q k z x y w p D.val.1 D.val.2-feeV q k z x y w p D.val.2 D.val.1
lemma spark_lane (D:PlaqAxes):
   XBridge q k (suba q k w (D,b,c)) (subb q k w (D,b,c)) β μx μy=↑(4*ff a b c*groupκ q k z x y w p D):= by
     unfold XBridge;
     unfold suba subb; simp_rw [gouge]; rw [skew₁ a c b]; change Complex.ofReal (4*ff a b c*feeV _ _ _ _ _ _ _ _ _)+ Complex.ofReal (4*(- ff a b c)*feeV _ _ _ _ _ _ _ _ _)=_; unfold groupκ; push_cast; ring
lemma ways (r:ℝ): ∑ a:U,skirt q k r w i a (veil z k (restB q p a)) μx μy=↑(4 * count G * (∑ u:PlaqAxes,dataF r i u * groupκ q k z x y w p u)):= by
     unfold skirt toll; rw [Finset.sum_comm]; simp_rw [Fintype.sum_prod_type]; -- at left? ∑ Ticket outside changed, nested complications. inspect
     simp_rw [spark_lane]; nth_rw 1 [show count G= ∑ b:U,∑ c:U,∑ a:U,(ff a b c ^ 2) from ?_]; swap; · unfold count; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
     rw [Complex.ofReal_mul,Complex.ofReal_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun d _=> ?_; push_cast; simp_rw [Finset.mul_sum,Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; ring
lemma pair_est (n:Lattice.Side)(e:ℝ)(x y w:Site n)(v:Tet)(u:Tet)(p:T) (r:ℝ):
    let X(i:Axis):=Wpv e (-1) u i n x w; let Y(i:Axis):=Wpv e (-1) v i n y w; ester n e r p u v x y w= ∑ t:PlaqAxes, dataF r p t*(X t.val.1*Y t.val.2-X t.val.2*Y t.val.1):= by intro X Y; exact (plaq_control (form r p) X Y (layout r p)).symm
def tithe (n:Lattice.Side)(e r:ℝ)(z x y w:Site n) (p i:Tet):= ∑ u:T,∑ v:T, segmentA n e z x y p u v * ester n e r i u v x y w
lemma weight_land (r:ℝ): ∑ d:PlaqAxes,dataF r i d * groupκ q k z x y w p d = tithe o ε r (K z) (K x) (K y) (K w) p i:= by
    unfold tithe groupκ feeV; simp_rw [← Finset.sum_sub_distrib,Finset.mul_sum,pair_est,Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun v _=> Finset.sum_congr rfl fun d _=> ?_; unfold nearA; -- let pair_est proof.X.
    ring
lemma processors (r:ℝ) : ∑ a:U,skirt q k r w i a (veil z k (restB q p a)) μx μy=↑(4* count G * tithe o ε r (K z) (K x) (K y) (K w) p i):= by rw [ways, weight_land]
end YM.PositionX.Sage
