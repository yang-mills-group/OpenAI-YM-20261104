import YM.X.Stems.Price
/-!
One rooted mark analytic Ward along shaped Links. Later used for evaluating clustered-open symbols, not on gauge-variant observables.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Jet Log MvPolynomial Next.Rank.Normal
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Pointwise
variable {G:Gauge} {n:ℕ} {b:Finset Cover}
variable {S:CoverConfig G→ℝ}

-- Derivative calculus with open Wick symbols, arbitrary real tests

def stroke (x:Brush G):= slit (Complex.ofReal ∘ text x)
lemma slit_deriv (p:Curly G)(f:ℝ→Brush G) (a:ℝ) (v:Brush G) (h:∀ i,HasDerivAt (fun t=> f t i) (v i) a): HasDerivAt (fun t=>snap (f t) p) (snap (f a) (stroke v p)) a:= by
   let D:(G.ColorIndex→ G.Color →L[ℝ] ℝ):=fun i=> EuclideanSpace.proj (𝕜:=ℝ) i
   induction p using MvPolynomial.induction_on with
   | C x=> simp only [stroke,slit_C,snap,aeval_C,_root_.map_zero]; exact hasDerivAt_const ..
   | add x y h g=> simp only [_root_.map_add]; exact h.add g
   | mul_X p i ih=> simp_rw [mul_comm p,stroke,slit_prod,map_add,map_mul,snap,aeval_X,aeval_C]; apply ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt a ((D i.2).hasFDerivAt.comp_hasDerivAt a (h i.1))).mul ih).congr_deriv; exact add_comm ..
lemma stroke_zero (p:Curly G): stroke 0 p=0:= slit_zero _
lemma stroke_add (p:Curly G)(x y:Brush G) : stroke (x+y) p=stroke x p+stroke y p:= by unfold stroke; rw [← slit_linear]; congr 2; ext1 i; exact Complex.ofReal_add ..
lemma stroke_scale (p:Curly G)(x:Brush G)(r:ℝ): stroke (r • x) p= (r:ℂ) • stroke x p:= by
   unfold stroke; rw [← slit_smul]; congr 2; ext1 i; exact Complex.ofReal_mul .. 

lemma slit_line (p:Curly G)(u v:Brush G) : HasDerivAt (fun t:ℝ=>snap (u+t • v) p) (snap u (stroke v p)) 0:= by
   convert slit_deriv p (fun r:ℝ=>u+r • v) 0 v _ using 1 -- infer? 
   · simp
   intro i; exact (by simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const (v i)|>.const_add (u i)) : HasDerivAt (fun r:ℝ=> u i+r • v i) (v i) 0)
lemma dream (H : Empirical b S)(r a:Brush G)(j:ℕ): snap r (stroke a (mark S ⟨b,H⟩ j)) = ((fderiv ℝ (jet (kind b S) j) (comb r) (comb a):ℝ):ℂ):= by
   have he:= slit_line (mark S ⟨b,H⟩ j) r a; simp_rw [mark_test, stamp_at H] at he
   have hc : HasDerivAt (fun t:ℝ=>comb (s:=b) (r+t • a)) (comb a) 0 := by simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const (comb (s:=b) a)).const_add (comb r))
   exact he.unique (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ (((show HasFDerivAt (jet (kind b S) j) _ (comb r) from ((Plausible.stamp ..).smooth.differentiable (by simp) (comb r)).hasFDerivAt).comp_hasDerivAt_of_eq _ hc (by simp)).congr_deriv rfl))

variable (HS:Small G S) (Y:ℝ→CoverConfig G) (x y:Brush G)
def page (Y:ℝ→CoverConfig G)(b:Finset Cover)(r:ℝ): Fine G b:= fun i=>record (fun t=> Y t i.val) r
variable (hi:∀ j<n, ∀ x:Brush G,someJ (along S x) j=0) (H:∀ i,Roots (fun t=>Y t i) (x i) (y i))
include H
lemma book_nice : ContDiffAt ℝ ω (page Y b) 0:=contDiffAt_pi.mpr fun i=>(H i.val).ok
lemma book (i:ℕ)(b:Finset Cover)(j:UsedEdges b): someJ (page Y b) i j= someJ (record (fun t=>Y t j.val)) i:= Eq.symm <| ((Act.linear (L:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:UsedEdges b=>G.Color) j) (show Act i (page Y b) (someJ (page Y b)) from ⟨book_nice Y x y H,fun _ _=> rfl⟩)).writes i le_rfl) -- params
lemma book_zero : someJ (page Y b) 0=0:= funext fun i=> by rw [book Y x y H 0 b, someJ_zero,(H i.val).zero];rfl
lemma book_one : someJ (page Y b) 1=comb x:= funext fun i=> (book Y x y H 1 b i).trans (H i.val).someL
lemma book_two : someJ (page Y b) 2=comb y:= funext fun i=> (book Y x y H 2 b i).trans (H i.val).someP
lemma book_eq (p:Empirical b S): S ∘ Y =ᶠ[𝓝 0] kind b S ∘ page Y b:= by
   filter_upwards [eventually_all.mpr fun i:UsedEdges b=>(H i.val).reverse] with t ht; dsimp only [kind,Function.comp_apply]; apply p.supported; intro i hi hx
   exact (ht (⟨i,hi,hx⟩:UsedEdges b)).symm.trans (congr_arg G.lieExp (congr_fun (take_extension (page Y b t)) (⟨i,hi,hx⟩:UsedEdges b)).symm) -- direction

include HS hi
lemma mark_rules {i:ℕ}(ht:i ≤ n+1): (↑(someJ (S ∘ Y) i:ℝ):ℂ)= if i=n then snap x (mark S HS n) else if i=n+1 then snap x (mark S HS (n+1))+ snap x (stroke y (mark S HS n)) else 0 := by
   obtain ⟨b,hb⟩:=HS
   have hQ j (hj:j<n) : jet (kind b S) j=0:=funext fun v:Fine G b=> by
      have hx:=hi j hj (extensionL b v); rw [stamp_at hb,take_extension] at hx; exact hx
   let p:=page Y b; have he : someJ (S ∘ Y) i=someJ (kind b S ∘ p) i:= by rw [someJ,someJ]; apply congr_arg ((i.factorial:ℝ)⁻¹ • ·); exact (book_eq Y x y H hb).iteratedDeriv_eq i
   rw [he,tick_base (n:=n) (kinds hb) (show Act (n+2) (page Y b) (someJ p) from ⟨book_nice Y x y H,fun _ _=> rfl⟩) (book_zero Y x y H) hQ ht]
   by_cases ha:i=n; · rw [if_pos ha,if_pos ha, mark_test, stamp_at hb, show someJ p 1=comb x from book_one Y x y H]
   by_cases hw:i=n+1
   · rw [if_neg ha,if_neg ha, if_pos hw,if_pos hw, mark_test, stamp_at hb, show someJ p 1=comb x from book_one Y x y H, show someJ p 2=comb y from book_two Y x y H, Complex.ofReal_add]; congr 1; exact (dream hb x y n).symm -- ] -- directions
   rw [if_neg ha,if_neg ha,if_neg hw,if_neg hw]; rfl
end YM.PositionX.Stems
