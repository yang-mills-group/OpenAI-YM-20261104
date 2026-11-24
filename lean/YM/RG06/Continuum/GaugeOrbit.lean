import YM.RG06.Continuum.RadialQuot
/-!
# Smooth change of gauge (derivative and curvature)

These are local field defining identities with the *same transformation convention as Wilson
links*, on any unscaled smooth continuum connection at all E4 positions. Gauge matrix logarithm
isn't needed: construct the logarithmic derivative by the actual color Lie projection and show
there is nothing to project by testing a Lie curve. Useful for proving the curvature-jet test
quotient on smooth connections via finite radial gauges. Not a continuum measure assertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Analysis Function
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G:Gauge}

abbrev Phase (G:Gauge):=E4 → G.El
def Ready (s:Phase G):= Good (G.mat ∘ s)
def face (s:Phase G):= G.mat ∘ s
def bar (s:Phase G):E4→G.Mat:=fun x=>star (face s x)
def shade (s:Phase G)(f:Continuum.Section G):Continuum.Section G:=fun x=> G.adjoint (s x) (f x)
def suffixM (s:Phase G)(j:Axis)(x:E4):G.Mat:=(par j (face s) x)*bar s x
def suffix (s:Phase G):Connection G:=fun i x=> G.projectColor (suffixM s i x)

lemma matou (s : Phase G)(f:Section G): (fun x=>G.colorMat (shade s f x))=fun x=>face s x * G.colorMat (f x) * bar s x:=by
  funext x; simp only [shade,G.mat_adjoint,Gauge.conjugate,face,bar,Function.comp_apply]
lemma Good.faces (s:Phase G)(h:Ready s):Good (bar s):=
  (show ContDiff ℝ ∞ (starL ℝ (A:=G.Mat)) from (starL ℝ (A:=G.Mat)).contDiff).comp h
lemma Good.shade (s:Phase G)(h:Ready s)(f:Section G)(hf:Good f): Good (Continuum.shade s f):=by
  rw [show Continuum.shade s f=fun x=>G.projectColor (face s x * G.colorMat (f x) * bar s x) from funext fun x=>rfl]
  exact G.projectColor.toContinuousLinearMap.contDiff.comp ((ContDiff.mul (show ContDiff ℝ ∞ (face s) from h) (G.colorMat.toContinuousLinearMap.contDiff.comp hf)).mul (Good.faces s h))
lemma Good.suffix (s:Phase G)(h:Ready s):Smooth (Continuum.suffix s):=by
  have he := (show Good (face s) from h)
  exact fun i=>G.projectColor.toContinuousLinearMap.contDiff.comp (ContDiff.mul (he.par i) (Good.faces s h))

@[simp] lemma pair_right (s:Phase G)(x:E4): face s x * bar s x=1:=G.mat_mul_star _
@[simp] lemma pair_left (s:Phase G)(x:E4): bar s x * face s x=1:=G.mat_star_mul _
lemma product_matrix {X Y:E4→G.Mat}(h:Good X)(ht:Good Y)(x:E4)(a:Axis) :
    par a (fun x=> X x*Y x) x=par a X x * Y x + X x*par a Y x :=by
   have he := ((h.germ x).hasFDerivAt.mul' (ht.germ x).hasFDerivAt).fderiv
   unfold par D
   erw [he,add_apply,smul_apply,smul_apply]; exact add_comm ..

lemma suffix_color (s:Phase G)(h:Ready s)(j:Axis)(x:E4): G.colorMat (suffix s j x)=suffixM s j x:=by
  apply G.colorMat_project_self
  rw [G.mem_lie]
  let f (t:ℝ):= G.mat (s (t • basis j + x) * (s x)⁻¹)
  refine G.tangent_generates (f:=f) ?_ ?_ (fun _=> ⟨_,rfl⟩)
  · have he : f = fun t=> face s (t • basis j + x)*bar s x:=by funext t; simp [f,G.mat_mul, G.mat_inv,face,bar]
    rw [he]
    have hg: HasDerivAt (fun t:ℝ=>t • basis j + x) (basis j) 0:=by simpa using! (((hasDerivAt_id (0:ℝ)).smul_const (basis j)).add_const x)
    have hh : HasFDerivAt (face s) (fderiv ℝ (face s) x) ((0:ℝ) • basis j+x):=by rw [zero_smul,zero_add]; exact ((show Good (face s) from h).germ x).hasFDerivAt
    exact ((hh.comp_hasDerivAt (0:ℝ) hg).mul_const (bar s x))
  unfold f; simp

lemma inv_deriv (s:Phase G)(h:Ready s)(j:Axis)(x:E4): par j (bar s) x=-(bar s x * par j (face s) x * bar s x):=by
  have he:par j (fun x=> face s x * bar s x) x=0:=by simp [par,D]
  rw [product_matrix (G:=G) (show Good (face s) from h) (Good.faces s h) x j] at he
  have hz:= congrArg (fun M => bar s x*M) (eq_neg_of_add_eq_zero_left he)
  simp only [mul_neg,← Matrix.mul_assoc,pair_left,one_mul] at hz
  -- hz : B F' B = -B F B' ; opposite
  rw [hz,neg_neg]

def shadeM (s:Phase G)(p:E4→G.Mat)(x:E4):=face s x *p x *bar s x
lemma shade_deriv (s:Phase G)(h:Ready s)(p:E4→G.Mat)(hp:Good p)(x:E4)(i:Axis):
    par i (shadeM s p) x=shadeM s (par i p) x + (suffixM s i x*shadeM s p x-shadeM s p x*suffixM s i x):=by
 unfold shadeM
 rw [product_matrix (X:=fun x=> face s x *p x) (ContDiff.mul h hp) (Good.faces s h),product_matrix (G:=G) (X:=face s) h hp,inv_deriv _ h]
 unfold suffixM
 simp only [add_mul,mul_neg,Matrix.mul_assoc]
 have he (p:G.Mat):bar s x * (face s x * p)=p:= by rw [←Matrix.mul_assoc,pair_left,one_mul]
 -- B * F' B = no cancel; other B*F cancel
 simp only [he]; abel

lemma ad_shade (s:Phase G)(h:Ready s)(p:Section G)(hp:Good p)(x:E4)(i:Axis):
    par i (shade s p) x=shade s (par i p) x + G.ad (suffix s i x) (shade s p x):=by
  have he (q:Section G)(a):G.colorMat (shade s q a)=shadeM s (fun x=> G.colorMat (q x)) a:=congr_fun (matou s q) _
  have hQ (q:Section G)(hq:Good q):par i (fun x=>G.colorMat (q x)) x=G.colorMat (par i q x):=(congr_fun (par_linear (G.colorMat.toContinuousLinearMap) hq i) x)
  apply G.colorMat_injective
  rw [← hQ (shade s p) (Good.shade s h p hp),map_add,G.colorMat_ad,suffix_color s h,
      he,he,show (fun x=> G.colorMat (shade s p x))=shadeM s (fun x=> G.colorMat (p x)) from matou s p,
      shade_deriv _ h (fun x=> G.colorMat (p x)) (G.colorMat.toContinuousLinearMap.contDiff.comp hp)]
  unfold shadeM; rw [hQ p hp]

lemma maurer (s:Phase G)(h:Ready s)(i j:Axis)(x:E4):
   par i (suffix s j) x - par j (suffix s i) x = G.ad (suffix s i x) (suffix s j x):=by
   have he (j i:Axis): G.colorMat (par i (suffix s j) x)=par i (suffixM s j) x:=by
      have hE:= par_linear (G.colorMat.toContinuousLinearMap) (Good.suffix s h j) i
      change G.colorMat _= _; rw [show suffixM s j=fun y=> G.colorMat (suffix s j y) from funext (fun y=>(suffix_color s h j y).symm)]; exact (congr_fun hE x).symm
   apply G.colorMat_injective
   rw [map_sub,he,he,G.colorMat_ad,suffix_color s h,suffix_color s h]
   unfold suffixM; have hF :Good (face s):=h
   rw [product_matrix (G:=G) (hF.par j) (Good.faces s h), product_matrix (G:=G) (hF.par i) (Good.faces s h),par_cross hF i j,inv_deriv s h,inv_deriv s h]
   noncomm_ring

variable (g:ℝ)
def dressed (A:Connection G)(s:Phase G): Connection G:=fun i=> shade s (A i) - g⁻¹ • suffix s i
lemma sound (A:Connection G)(h:Smooth A)(s:Phase G)(hs:Ready s):Smooth (dressed g A s):=fun i=>
 ContDiff.sub (Good.shade s hs _ (h i)) (ContDiff.const_smul g⁻¹ (Good.suffix s hs i))
lemma changes (hg:g≠0)(A:Connection G)(h:Smooth A)(s:Phase G)(hs:Ready s)(i j:Axis):
    curvature g (dressed g A s) i j=shade s (curvature g A i j):=by
  let B:= suffix s
  let T(i:Axis):=shade s (A i)
  funext x
  unfold curvature dressed
  rw [sub_eq_add_neg,sub_eq_add_neg,par_add (g:=-(g⁻¹ • suffix s j)) (Good.shade s hs _ (h j)) (ContDiff.neg (ContDiff.const_smul g⁻¹ (Good.suffix s hs j))), par_add (g:=-(g⁻¹ • suffix s i)) (Good.shade s hs _ (h i)) (ContDiff.neg (ContDiff.const_smul g⁻¹ (Good.suffix s hs i))),par_neg,par_neg,par_scale _ (Good.suffix s hs j),par_scale _ (Good.suffix s hs i)]
  simp only [bracket,Pi.smul_apply,Pi.add_apply,Pi.neg_apply,ad_shade s hs _ (h _), shade,map_add,map_neg,map_smul,LinearMap.add_apply,LinearMap.neg_apply,LinearMap.smul_apply,smul_add,smul_neg,smul_smul,mul_inv_cancel₀ hg,one_smul, rot_bracket]
  rw [bracket_anti (a:=((G.adjoint (s x)) (A i x))) (b:=suffix s j x),← mul_assoc, mul_inv_cancel₀ hg,one_mul, ← maurer s hs, smul_sub]; abel
lemma shepherd (hg:g≠0)(A:Connection G)(f:Section G)(hf:Good f)(s:Phase G)(hs:Ready s)(i:Axis):
    covariant g (dressed g A s) i (shade s f)=shade s (covariant g A i f):=by
  funext x; unfold covariant dressed
  simp only [bracket,Pi.add_apply,Pi.sub_apply, Pi.smul_apply,ad_shade s hs f hf,shade,map_sub,map_add,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_sub,smul_smul,mul_inv_cancel₀ hg,one_smul,rot_bracket]
  abel

lemma at_depth (hg:g≠0)(A:Connection G)(h:Smooth A)(s:Phase G)(hs:Ready s){j:ℕ}(w:Fin j→ Axis)(a b:Axis):
    nablas g (dressed g A s) w (curvature g (dressed g A s) a b)=shade s (nablas g A w (curvature g A a b)):=by
   induction j with
   | zero=> exact changes g hg A h s hs a b
   | succ j H=> rw [nablas,H,shepherd g hg A _ (Smooth.higherCov g A h _ _ (Smooth.F g A h _ _)) s hs,nablas]
lemma center_same (hg:g≠0)(A:Connection G)(h:Smooth A)(s:Phase G)(hs:Ready s)(h0:s 0=1):
    Form.evaluate g (dressed g A s) 0 = Form.evaluate g A 0 :=by
  funext j a b w; unfold Form.evaluate covJet; rw [at_depth g hg A h s hs, shade,h0,G.adjoint_one]
end YM.RG06.Continuum
