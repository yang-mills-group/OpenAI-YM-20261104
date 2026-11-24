import YM.X.Gravity.Oracle
import YM.X.Grow.Hue
/-!
# Full color action on honest FO tensor. naturality including multi-hit. Not only connected comp.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "K"=>Book G
local notation "e"=>epsilon q
local notation "Q"=>flow G
variable (t:G.El)
lemma along_fixed {f: CoverConfig G→ℝ}(hf: GaugeInvariant f)(A:Brush G): along f (signL t A)=along f A:= by
   funext r; unfold along; rw [← map_smul]; refine (congr_arg f (show posit (signL t (r • A))= Lattice.gauge (fun i=>t) (posit (r • A)) from ?_)).trans (hf _ _)
   funext i; change G.lieExp (G.adjoint t _) = t*G.lieExp _*t⁻¹; apply G.mat_injective; simp only [G.mat_mul,G.mat_lieExp,G.mat_inv,G.mat_adjoint]; exact G.exp_conjugate ..
def matte (p:Pin)(A:G.Color): Fan G:=∑ i:G.ColorIndex,Finsupp.single (p,i) (A i)
lemma matte_look (x:Brush G)(p:Pin)(A:G.Color) : flatL x (matte p A)= inner ℝ A (x p):= by unfold flatL matte;rw [map_sum]; simp only [Finsupp.linearCombination_single,Braid.paint_norm]; rfl
local notation "T"=>G.ColorIndex
lemma tintK (x y:G.Color): inner ℝ (G.adjoint t x) (G.adjoint t y)=inner ℝ x y := (LinearIsometry.inner_map_map (⟨G.adjoint t,G.norm_adjoint t⟩:G.Color→ₗᵢ[ℝ] G.Color)) x y
lemma tilt_K (x y:G.Color): inner ℝ (G.adjoint t⁻¹ x) y=inner ℝ x (G.adjoint t y):= by rw [← tintK t,← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
lemma matte_green (n:Side)(x y:Pin) (A:G.Color)(k:T) : paints n (matte x A) y k=(if y.2=x.2 then Braid.cane n y.1 x.1 else 0)* A k:= by
   change text (paints n (matte x A)) (y,k)=_; rw [text_paints]; unfold matte;rw [map_sum]; simp_rw [Finsupp.linearCombination_single,tau]; rw [Finset.sum_eq_single k]; simp only [and_true, true_and,smul_eq_mul]; rw [mul_comm]; intro b _ he; simp [he,he.symm]; simp
lemma matte_k (n:Side)(x y:Pin) (A B:G.Color) : flatL (paints n (matte x A)) (matte y B)=(if y.2=x.2 then Braid.cane n y.1 x.1 else 0)* inner ℝ B A:= by rw [matte_look]; simp_rw [paint_norm,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [matte_green n x y A]; ring
lemma matting (x:Pin)(k:T): matte (G:=G) x (tan k)= Finsupp.single (x,k) 1 := by unfold matte; unfold tan;rw [Finset.sum_eq_single k]; all_goals simp_all [EuclideanSpace.basisFun_apply]
-- exchanged glyph image
local notation "H"=>Hair G
def robe (i: Hair G): H→₀ℂ:= Stems.com (matte i.1 (G.adjoint t⁻¹ (tan i.2)))
def tonal : Curly G →ₐ[ℂ] Curly G:= exchange (robe t)
lemma robe_point (A:Brush G)(i:Hair G): snap A (tonal t (X i))= snap (signL t A) (X i):= by rw [tonal,exchange_x,robe,carbon,matte_look,tilt_K,snap,aeval_X]; apply congr_arg; exact EuclideanSpace.basisFun_inner ..
lemma tonal_eval (A:Brush G)(p:Curly G): snap A (tonal t p)= snap (signL t A) p:= by apply DFunLike.congr_fun (f:=(snap A).comp (tonal t)); ext1 i; exact robe_point t A i
lemma color_scope (n:Side) : scope (robe t) (Q n)= Q n:= by
   refine Symmetric.ext (funext fun i=>funext fun j=> ?_); let x:= i.1; let y:= j.1; change treats (flow G n) (robe t i) (robe t j)=_; unfold robe; rw [cornered,matte_k,tintK]; let a:= (fun p:H=> Stems.com (matte p.1 (tan p.2)));
   rw [← matte_k n i.1 j.1 (tan i.2), ← cornered]; simp_rw [matting ..]; -- map color com
   simp_rw [com_six]; change treats (flow G n) _ _ = _; simp [treats]
end YM.PositionX.Gravity
