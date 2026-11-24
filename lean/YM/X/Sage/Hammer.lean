import YM.X.Sage.Drain
/-!
# V3 stencil bridge. cubic classical part and topological primitive. Stone means one extra power.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V:Type*} {q:ℕ+} {r R:ℝ}
local notation "L"=> (atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "θ"=> Reed.Horizontal G
local notation "Θ"=> (⊤:Submodule ℝ (Fan G))
local notation "T"=> Tet
local notation "A"=>PlaqAxes
section brush
variable [CommRing V] [Algebra ℂ V] (g f t:G.ColorIndex→ V)(a x y: G.ColorIndex)
def hook (a:U)(f g:G.ColorIndex→ V):V:= ∑ x:U,∑ y:U,(ff a x y:ℂ) • (f x*g y)
def coreK (a:U)(f g:U→ V):V:= ∑ x:U,∑ y:U,(iv a x y:ℂ) • (f x*g y)
lemma hook_flips : hook a f g= -hook a g f:= by unfold hook; rw [Finset.sum_comm]; simp only [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; rw [skew₁ a i j]; push_cast; rw [neg_smul,neg_neg,mul_comm]
lemma hook_lack : hook a f f=0:= by
    have he:= hook_flips f f a; suffices h:(2:ℂ) • hook a f f=0 from (smul_eq_zero.mp h).resolve_left (by norm_num); rw [two_smul]; nth_rw 1 [he]; exact neg_add_cancel .. -- check
lemma hook_double : coreK a f g= (1/2:ℂ) • hook a f g:= by unfold hook coreK; simp_rw [Finset.smul_sum,smul_smul,ffor,Complex.ofReal_mul]; norm_num [← mul_assoc]
lemma cubic_hook : cubicP f g t= ∑ a:U, f a*hook a g t:= by unfold cubicP hook; simp_rw [Finset.mul_sum, mul_smul_comm]
lemma cubic_left (x:U→V): cubicP (f+g) t x=cubicP f t x + cubicP g t x:= by unfold cubicP; simp [Finset.sum_add_distrib, add_mul,smul_add]
lemma cubic_mid (x:U→V): cubicP f (g+t) x=cubicP f g x+cubicP f t x:= by unfold cubicP; simp [Finset.sum_add_distrib, add_mul, mul_add,smul_add]
lemma cubic_right (x:U→V): cubicP f g (t+x)= cubicP f g t + cubicP f g x:= by unfold cubicP; simp [Finset.sum_add_distrib, mul_add,smul_add]
lemma cubic_sub (x:U→V):cubicP (f-g) t x=cubicP f t x-cubicP g t x:= by unfold cubicP; simp [sub_mul,smul_sub, Finset.sum_sub_distrib]
lemma cubic_minus : cubicP f g t= -cubicP f t g:= by simp_rw [cubic_hook, hook_flips (g:=t) (f:=g),mul_neg,Finset.sum_neg_distrib]
end brush
local notation "P"=> Curly G
variable (v:PlaqAxes)(a:G.ColorIndex)
def potentialL (i:Axis)(a:G.ColorIndex): P:= X ((0,i),a)
def arcF (v:PlaqAxes)(a:U):= faceText v a
def old (v:PlaqAxes)(a:U): Curly G:= ∑ i:U,∑ j:U,(iv a i j:ℂ) • shiftProduct v i j
def classicV (v:PlaqAxes): P := ∑ i:U,faceText v i*glove (v,i)
lemma vet : vertex (G:=G) v=∑ i:U,faceText v i*old v i:= by rw [Stems.trinity]; simp_rw [old,Finset.mul_sum, mul_smul_comm]
lemma jest : glove (v,a)= hook a (potentialL v.val.1) (potentialL v.val.2):= rfl
lemma hcsub {p q:Normal.poly V}(h:HC p k)(he:HC q k): HC (p-q) k:= by rw [leafy, map_sub,leafy.mp h,leafy.mp he]
lemma hcmul {p q:Normal.poly V}(h:HC p 1)(he:HC q 1): HC (p*q) 2:=h.mul he
local notation "H"=> Heat.Top.cut
lemma shiftProduct_hc (u v':G.ColorIndex): HC (shiftProduct v u v') 2:= by
    unfold shiftProduct; dsimp only;
    repeat' (first | apply IsWeightedHomogeneous.add | apply hcsub | apply hcmul | exact isWeightedHomogeneous_X ..)
lemma old_h : HC (old v a) 2:= by unfold old; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; rw [← C_mul']; exact (shiftProduct_hc v i j).C_mul _
lemma projector (i j:U) : pressP (shiftProduct v i j)= potentialL v.val.1 i * potentialL v.val.2 j - (potentialL v.val.1 i * potentialL v.val.1 j + potentialL v.val.2 i * potentialL v.val.1 j) - potentialL v.val.2 i * potentialL v.val.2 j:= by unfold shiftProduct potentialL pressP; dsimp only; simp only [vanishZ,map_add,map_sub,map_mul,rename_X]; ring
lemma sense : pressP (old v a)= glove (v,a):= by
    unfold old; simp_rw [map_sum,map_smul,projector,smul_sub,smul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]; let f:=potentialL (G:=G) v.val.1; let g:=potentialL (G:=G) v.val.2; change coreK a f g-(coreK a f f+coreK a g f)-coreK a g g=_; rw [jest]; change _= hook a f g; simp_rw [hook_double,hook_lack,smul_zero,zero_add,sub_zero]; rw [hook_flips (f:=g) (g:=f),smul_neg,sub_neg_eq_add,← add_smul]; norm_num
lemma standby : Stone Θ 2 (old v a) (glove (v,a)):= sense v a ▸ pressureP _ (old_h ..)
lemma face_h : HC (faceText v a) 1:= by rw [faceText,←com_text]; exact HCglyph ..
lemma face_v : faceText v a∈ verse Θ 2:= by rw [faceText,← com_text]; exact verse_glyph (k:=1) (arc_occ (0,v,a)) (by simp)
lemma stone_mulF {p q p1 q1:Curly G} {W:Submodule ℝ (Fan G)} {u:ℕ}(hu:u=d+k)(h:Stone W d p p1)(g:Stone W k q q1): Stone W u (p*q) (p1*q1):= hu.symm ▸ h.mul g
lemma valve : Stone (G:=G) Θ 4 (vertex v) (classicV v):= by rw [vet,classicV]; exact Stone.sums _ fun i _=> stone_mulF (d:=2) (k:=2) rfl (Stone.along (face_v v i)) (standby v i)
end YM.PositionX.Sage
