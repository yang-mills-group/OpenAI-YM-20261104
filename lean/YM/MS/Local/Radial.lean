import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Differential
/-!
# Differentiate local polynomial identity at one slot

Antifield turns and curvature decomposition by exact Euler-degree division.
Complex amplitudes as in the momentum conventions; take conjugate later for real
covariant stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.Radial
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open Landau Detect Detect.Mark
open Complex (I)
open scoped Topology ContDiff
variable {G : Gauge} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {h:ℤ}
variable {f : E → ℂ}

lemma shape_der (hx : Plane.Shape f h) (v : E) : Plane.Shape (Analysis.D v f) (h-1) := by
   rcases lt_or_ge h 0 with he|he
   · rw [show Analysis.D v f=0 from by rw [hx.charge he]; ext; simp [Analysis.D]]; exact form_zero _ -- `simp` maybe
   lift h to ℕ using he
   have hs : Tensor.Sym (coeff f h 0):= Tensor.coeff_symm (hx.smooth.contDiffAt.of_le (by exact_mod_cast le_top)); have h0:= hx.form
   cases h with
   | zero=>
           have hL : f=(fun _=> f 0):= funext fun x=> shape_constant hx x
           rw [show Analysis.D v f=0 from by rw [hL]; ext; simp [Analysis.D]]; exact form_zero _
   | succ h=>
       let U : Tensor.T E ℂ (h+1):= Tensor.coeff f (h+1) 0
       have hU x : Analysis.D v f x= Tensor.diagonal (((h+1:ℕ):ℝ) • U.curryLeft v) x:= by
           rw [Analysis.D]; nth_rw 1 [h0]; rw [Tensor.differential_diagonal _ hs]; simp [Tensor.diagonal,U]; -- simp nsmul
       rw [funext hU]; exact form_diag _ _ (by omega)

variable {u : Axis → FourP→ℂ}
def square (i : Axis) (f : FourP→ℂ) (x: FourP):= Analysis.D (spike i) f x
def div (u : Axis → FourP→ℂ) := fun x=> ∑ i:Axis, square i (u i) x
lemma div_shape (hU : ∀ i, Plane.Shape (u i) h): Plane.Shape (div u) (h-1):= by
    convert Plane.Shape.sum (s:=Finset.univ) (fun i _=> shape_der (hU i) (spike i)) using 1; ext; rw [Finset.sum_apply]; rfl
lemma euler {f:FourP→ℂ} (hU : Plane.Shape f h) (x:FourP): ∑ i:Axis,(x i:ℂ)*square i f x=(h:ℂ)*f x:= by
    have he : fderiv ℝ f x x= (h:ℝ) • f x := by
       rcases lt_or_ge h 0 with he|he
       · rw [hU.charge he]; simp
       lift h to ℕ using he; let U:=Tensor.coeff f h 0; have ht : Tensor.Sym U:= Tensor.coeff_symm (hU.smooth.contDiffAt.of_le (by exact_mod_cast le_top))
       have hh : f= Tensor.diagonal U:= hU.form
       rw [hh]; simpa using Euler _ ht x
    have hE := congr_arg (fderiv ℝ f x) (slam x); rw [he] at hE; simpa only [map_sum,map_smul,Int.cast_natCast,Complex.real_smul,Complex.ofReal_intCast,square, Analysis.D] using hE

lemma square_slot (i a : Axis) (p : FourP) : square i (fun q:FourP=> (q a:ℂ)) p= if i=a then 1 else 0:= by
   unfold square Analysis.D; let V:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Axis=>ℝ) a; change fderiv ℝ (⇑(Complex.ofRealCLM.comp V)) p _=_; rw [(Complex.ofRealCLM.comp V).fderiv]; by_cases h:i=a ; simp [V,h]; simp [V,h,Ne.symm h] -- `Ne.symm h` wrong
lemma product (i a:Axis) {f:FourP→ℂ} (hf:Plane.Shape f h) (x): square i (fun x:FourP=> (x a:ℂ)*f x) x = (if i=a then f x else 0)+(x a:ℂ)*square i f x := by
   have he: ContDiff ℝ ∞ fun x:FourP=> (x a:ℂ):= Complex.ofRealCLM.contDiff.comp ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Axis=>ℝ) a).contDiff)
   unfold square Analysis.D; rw [fderiv_fun_mul (he.differentiable (by simp) _) (hf.smooth.differentiable (by simp) _)]
   have hv:=square_slot i a x
   unfold square Analysis.D at hv; simp [hv,mul_ite]; ring

lemma taken (hx : ∀ i, Plane.Shape (u i) h) (he : ∀ p a i, ((p:FourP) a:ℂ)*u i p=(p i:ℂ)*u a p) (x:FourP) i :
    ((h:ℂ)+3)*u i x=(x i:ℂ)*div u x:= by
   have hv a := congr_arg (fun f:FourP→ℂ=>square a f x) (show (fun p:FourP=> (p a:ℂ)*u i p)=(fun p:FourP=> (p i:ℂ)*u a p) from funext (fun p=> he p a i))
   have h' : ∑ a:Axis, square a (fun p:FourP=> (p a:ℂ)*u i p) x=∑ a:Axis, square a (fun p:FourP=>(p i:ℂ)*u a p) x:= sum_congr rfl fun i _=>hv i
   simp only [product _ _ (hx _),Finset.sum_add_distrib,← Finset.mul_sum,↓reduceIte] at h'
   unfold div; simp [euler (hx i)] at h'; linear_combination h'

-- curvature decomposition: strictly horizontal vector symbol is curl of antisym primitive
lemma curl (hx : ∀ i, Plane.Shape (u i) h) (he : ∀ p:FourP, ∑ i:Axis,(p i:ℂ)*u i p=0) (x:FourP) i :
   ((h:ℂ)+1)*u i x=∑ a:Axis,(x a:ℂ)*(square a (u i) x-square i (u a) x):= by
   have hv := congr_arg (fun f:FourP→ℂ=> square i f x) (funext he); -- differentiate sum
   simp_rw [mul_sub, Finset.sum_sub_distrib, euler (hx i)]; change square i (fun p:FourP=> ∑ i:Axis,(p i:ℂ)*u i p) x = square i (fun _=>0) x at hv
   have hc (i:Axis): ContDiff ℝ ∞ fun p:FourP=> (p i:ℂ)*u i p:= by refine ContDiff.mul ?_ (hx i).smooth; exact Complex.ofRealCLM.contDiff.comp ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Axis=>ℝ) i).contDiff)
   have he : ∑ a:Axis,square i (fun p:FourP=>(p a:ℂ)*u a p) x=0:= by
      unfold square Analysis.D at hv; rw [fderiv_fun_sum (fun i _=> (hc i).differentiable (by simp) _)] at hv; simpa [square,Analysis.D] using hv
   simp only [product _ _ (hx _),Finset.sum_add_distrib] at he; simp at he; linear_combination he
end YM.MS.Local.Radial
