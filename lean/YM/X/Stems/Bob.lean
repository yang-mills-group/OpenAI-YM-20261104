import YM.X.Stems.Flick
/-!
One rooted Ward `δ A=dε` with first change as required, using no BRST/Slavnov assumptions. Local before passing to shell.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Gauge Source ProjectorNext.Calibration Gauss Jet Log MvPolynomial Next.Rank.Normal
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Pointwise
variable {G:Gauge} {n:ℕ} {S:CoverConfig G→ℝ}

lemma shift_skew (a b : G.Color): Log.shift a b= -Log.shift b a:= by unfold Log.shift; rw [← smul_neg]; apply congr_arg; apply G.colorMat_injective; simp [G.colorMat_ad]
variable (δ:Cover→G.Color)
def raised : Brush G:= fun i=> δ (i.1+step i.2)-δ i.1
def θ : Brush G →ₗ[ℝ] Brush G:= LinearMap.pi (fun i => G.ad.flip ((1/2:ℝ) • (δ (i.1+step i.2)+δ i.1)) ∘ₗ LinearMap.proj i)
def sinking : Brush G := fun i=> Log.shift (-δ i.1) (δ (i.1+ step i.2))

variable (x:Brush G)
def glossy (z r:ℝ) : CoverConfig G:= gauge (fun i=>G.lieExp (r • ((-z) • δ i))) (posit (r • x)) -- check sign! gauge want minus site; gives slope + z (δtop-δbase) ?? gauge uses e- t? state start minus, end inverse +
lemma gloss (e:Pin)(z:ℝ): Roots (fun r=> glossy δ x z r e) ((x+z • raised δ) e) ((z • θ δ x + (z*z) • sinking δ) e):= by
   let a:= δ e.1; let b:= δ (e.1+step e.2);let l:=(-z) • a; let k:= z • b
   have he (r:ℝ): glossy δ x z r e= (G.lieExp (r • l)* G.lieExp (r • x e))*G.lieExp (r • k):= by unfold glossy Lattice.gauge;dsimp [l,k]; rw [neg_smul z b,smul_neg,Work.F03.exp_neg_color];simp [posit,a]
   rw [funext he]; let q (x y:G.Color):=G.ad x y; have hh:= ((Roots.Exponent l).times (Roots.Exponent (x e))).times (Roots.Exponent k); convert hh using 1
   · rfl
   · change x e + z • (b-a) =l+x e+k; dsimp only [l,k]; rw [neg_smul,smul_sub];abel
   change z • q (x e) ((1/2:ℝ) • (b+a)) + (z*z) • Log.shift (-a) b = _; simp only [zero_add,add_zero]
   rw [shift_skew l (x e)]
   change z • G.ad (x e) ((1/2:ℝ)•(b+a)) + _ =_; simp only [Log.shift,l,k,map_add,map_smul,map_neg,neg_smul, LinearMap.add_apply,LinearMap.neg_apply,LinearMap.smul_apply,smul_smul,smul_neg,neg_neg,smul_add]
   -- linear commutatives
   module

lemma base_line_deriv (v:Brush G)(i:Pin): HasDerivAt (fun t:ℝ=> (x+t • v) i) (v i) 0:= by
     change HasDerivAt (fun t:ℝ=> x i+t • v i) (v i) 0; simpa using (((hasDerivAt_id' (0:ℝ)).smul_const (v i)).const_add (x i))
variable (HS:Small G S) (hi:∀ j<n, ∀ x:Brush G,someJ (along S x) j=0)(hG:GaugeInvariant S)
include hi hG
lemma low_rose (z:ℝ): snap (x+ z • raised δ) (mark S HS n)= snap x (mark S HS n):= by
    have h:= mark_rules HS (glossy δ x z) (x + z • raised δ) (z • θ δ x +(z*z)•sinking δ) hi (fun i=> gloss δ x i z) (i:=n) (by omega)
    rw [show S ∘ glossy δ x z= along S x from funext (fun i=>hG ..),← mark_test HS n,if_pos rfl] at h; exact h.symm
lemma still : stroke (raised δ) (mark S HS n)=0:= by
    apply snap_ext; intro u; rw [map_zero]
    have ht:= slit_line (mark S HS n) u (raised δ); simp_rw [low_rose δ u HS hi hG] at ht
    exact ht.unique (hasDerivAt_const ..)
lemma high_rose (z:ℝ): snap x (mark S HS (n+1))= snap (x+z • raised δ) (mark S HS (n+1))+snap (x+z • raised δ) ((z:ℂ) • stroke (θ δ x) (mark S HS n)+((z*z:ℝ):ℂ) • stroke (sinking δ) (mark S HS n)):= by
    have h:= mark_rules HS (glossy δ x z) (x + z • raised δ) (z • θ δ x +(z*z)•sinking δ) hi (fun i=> gloss δ x i z) (i:=n+1) le_rfl
    rw [show S ∘ glossy δ x z= along S x from funext (fun i=>hG ..), ← mark_test HS (n+1),if_neg (by omega),if_pos rfl,stroke_add,stroke_scale,stroke_scale] at h
    exact h
lemma high_price : snap x (stroke (raised δ) (mark S HS (n+1)))= -snap x (stroke (θ δ x) (mark S HS n)):= by
    let m:= mark S HS n;let p:= mark S HS (n+1); let L := θ δ x; let D:=stroke L m; let u:= stroke (sinking δ) m; let f(y:Curly G)(t:ℝ):= snap (x+t • raised δ) y
    have he (t:ℝ): snap x p= f p t + ((t:ℂ)*f D t+(t:ℂ)*(t:ℂ)*f u t):= by
       rw [show p=mark S HS (n+1) from rfl, high_rose δ x HS hi hG t]; simp only [map_add,map_smul, Complex.ofReal_mul,smul_eq_mul]; rfl
    have h f' := slit_line f' x (raised δ)
    have hl : HasDerivAt Complex.ofReal 1 0:= by simpa using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt -- using using Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have hh := (h p).add ((hl.mul (h D)).add ((hl.mul hl).mul (h u))); apply eq_neg_of_add_eq_zero_left
    exact Eq.symm ((show (0:ℂ)=snap x (stroke (raised δ) p)+snap x D from by convert (hasDerivAt_const (x:=0) (c:=snap x p)).unique ((hh : HasDerivAt (fun t:ℝ=> f p t+((t:ℂ)* f D t+(t:ℂ)*(t:ℂ)* f u t)) _ _).congr_of_eventuallyEq (Filter.Eventually.of_forall he)) using 1 <;> simp))
end YM.PositionX.Stems
