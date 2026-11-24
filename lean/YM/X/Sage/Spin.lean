import YM.X.Chir.Livery
/-!
# Prototype T mark algebra. rational internal orientation; exact declared real axes and coefficients. Gauge.Color metric.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Hue Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {m d:ℕ} {V:Type*} {r R:ℝ}
local notation "K"=> Poly PlaqAxes G
local notation "U"=> G.ColorIndex
local notation "P"=>PlaqAxes
local notation "T"=>Tet
variable (p t v:Tet) (x y z:G.ColorIndex)
/- T rational prefix. φ* sqrt factors separate. Static. -/
def dataF (r:ℝ)(p:Tet)(w:P) := form r p w.val.1 w.val.2
def Emitter (r:ℝ)(p:Tet)(x:G.ColorIndex): poly (CoverC G):= ∑ w:P, Complex.ofReal (dataF r p w) • MvPolynomial.X (w,x)
def cubicP (f g h:G.ColorIndex→V)[CommRing V][Algebra ℂ V]:V:= ∑ a:U,∑ b:U,∑ c:U,(ff a b c:ℂ) • (f a*(g b *h c))
def cone (r:ℝ)(M:PanelL G)(p:Tet): G.Color := ∑ i:P, dataF r p i • M i
lemma displays (M:PanelL G)(r:ℝ): display M (Emitter r p x)= ↑(cone r M p x):= by unfold display Emitter cone; simp only [map_sum,map_smul,aeval_X, show ∀ f:P→G.Color,(∑ i,f i).ofLp x= ∑ i,f i x from fun f=>map_sum (EuclideanSpace.proj x:G.Color→L[ℝ] ℝ) f Finset.univ,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_sum, Complex.ofReal_mul] -- sum name
lemma vpects (r:ℝ)(M:PanelL G)(v:G.El): cone r (Hue.tint v M) p=G.adjoint v (cone r M p):= by unfold cone; rw [map_sum]; simp_rw [map_smul]; rfl
-- STRUCT ff calibration and strictness
lemma ffl : ff x y z=Inner.inner ℝ (tan x) (G.ad (tan y) (tan z)):= by unfold ff tan; rw [EuclideanSpace.basisFun_inner]
lemma skew₁ : ff x y z= -ff x z y:= by rw [ffl,ffl, StressFlux.ad_antisym (tan z), inner_neg_right,neg_neg]
lemma skew₂ : ff x y z= -ff z y x:= by rw [ffl,ffl, real_inner_comm,Gauge.ad_skew]
lemma skew₀ : ff x y z=ff z x y:= by rw [skew₂, skew₁ z,neg_neg]
lemma skew₃ : ff x y z=ff y z x:= by rw [skew₀ y]
lemma ffor : ff x y z = 2*iv x y z:=by unfold iv Log.shift; rw [ffl,real_inner_smul_right]; ring
lemma lack (he:¬(x≠y∧y≠z∧z≠x)): ff x y z=0:= by rw [ffor,skip_tan x y z he,mul_zero]
lemma bc_ad (u:G.El)(x y:G.Color): G.ad (G.adjoint u x) (G.adjoint u y)=G.adjoint u (G.ad x y):= by
   apply G.colorMat_injective; simp only [Gauge.colorMat_ad,Gauge.mat_adjoint,Gauge.conjugate]; simp [mul_assoc,mul_sub,sub_mul,← mul_assoc (star (G.mat u)) (G.mat u)] -- mat_star_mul
lemma bc_sk (x y z:G.Color): Inner.inner ℝ x (G.ad y z)= Inner.inner ℝ y (G.ad z x):= by rw [StressFlux.ad_antisym y z, inner_neg_right, real_inner_comm (G.ad z y) x,Gauge.ad_skew z y x,neg_neg]

def ward (G:Gauge): poly (CoverC G):= cubicP (Emitter 1 0) (Emitter 1 1) (Emitter 1 2)
def tune (G:Gauge): poly (CoverC G) := ∑ a:T,∑ x:G.ColorIndex,Emitter (-1) a x * Emitter (-1) a x
lemma crest (f g h:G.ColorIndex→V)[CommRing V][Algebra ℂ V]: cubicP f g h=cubicP g h f:= by unfold cubicP; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro a _; rw [skew₃ a]; ring_nf -- smul reorder
lemma volw (M: PanelL G): Hue.display M (ward G)= ↑(Inner.inner ℝ (cone 1 M 0) (G.ad (cone 1 M 1) (cone 1 M 2)) :ℝ):= by
   unfold ward cubicP; rw [aspect]; simp_rw [map_sum,map_smul, map_mul, displays,Complex.ofReal_sum,Complex.ofReal_mul,smul_eq_mul, mul_assoc]
lemma volt (M: PanelL G): Hue.display M (tune G)= ↑(∑ i:T, Inner.inner ℝ (cone (-1) M i) (cone (-1) M i):ℝ):= by
    unfold tune; simp_rw [map_sum,map_mul,displays,paint_norm,Complex.ofReal_sum,Complex.ofReal_mul]
lemma evenV (r:ℝ): HC (Emitter r p x) 1:= by unfold Emitter; apply IsWeightedHomogeneous.sum; intro i _; rw [← C_mul']; exact (isWeightedHomogeneous_X ..).C_mul _
lemma standing : HC (ward G) 3:= by unfold ward cubicP; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.sum; intro k _; rw [← C_mul']; exact ((evenV ..).mul ((evenV ..).mul (evenV ..))).C_mul _
lemma standing₀ : HC (tune G) 2:= by unfold tune; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; exact (evenV ..).mul (evenV ..)
lemma wc : Fixed (ward G):= by intro v x; rw [volw,volw,vpects,vpects,vpects,bc_ad,StressFlux.inner_adjoint]
lemma vc : Fixed (tune G):= by intro v x; rw [volt,volt]; simp_rw [vpects,StressFlux.inner_adjoint]
lemma vivid₁ : Hue.Clear (ward G):= fun x=>by rw [volw]; simp
lemma vivid₀ : Hue.Clear (tune G):= fun x=>by rw [volt]; simp
lemma faith (hg:G.Simple): ∃ x y z:G.ColorIndex, ff x y z≠0:= by
   obtain ⟨a,b,hb⟩:= hg.nonabelian; by_contra! h; apply hb; ext i; rw [axel]; simp [h]
def count (G:Gauge):ℝ:= ∑a:G.ColorIndex,∑b:G.ColorIndex,∑c:G.ColorIndex, (ff a b c)^2
lemma counted (h:G.Simple): 0<count G:= by
    obtain ⟨a,b,c,H⟩:=faith h; unfold count; apply Finset.sum_pos'; · exact fun _ _=> Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> sq_nonneg _
    exact ⟨a,Finset.mem_univ _, Finset.sum_pos' (fun _ _=> Finset.sum_nonneg fun _ _=>sq_nonneg _) ⟨b,Finset.mem_univ _,Finset.sum_pos' (fun _ _=>sq_nonneg _) ⟨c, Finset.mem_univ _, sq_pos_of_ne_zero H⟩⟩⟩ -- indentation
end YM.PositionX.Sage
