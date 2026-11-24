import YM.Integration.WilsonRootedPosteriorConnected

/-! Center the four completely unnormalized one-occurrence numerators
before the first absolute value. Only the total partition appears. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedUnnormalizedHearing
open Function Filter MeasureTheory RG
open scoped Topology BigOperators Classical
variable {X:Type*}[MeasurableSpace X](μ:Measure X)
def concert (m d:X→ℂ)(t:ℂ):ℂ:=∫x,m x+t*d x ∂μ

def hearing (o a b j v u h k:X→ℂ)(t:ℂ):ℂ:=
  let z:=concert μ o v t
  concert μ j k t/z-(concert μ a u t/z)*(concert μ b h t/z)

def center (α β c:ℂ)(v u h k:X→ℂ)(x:X):ℂ:=k x-α*h x-β*u x+(α*β-c)*v x

theorem window {z a b j v u h k:ℂ}(pos:z≠0):
    let α:=a/z
    let β:=b/z
    let c:=j/z-α*β
    k/z-(v*j+u*b+h*a)/z^2+2*v*a*b/z^3=(k-α*h-β*u+(α*β-c)*v)/z:=by
  dsimp
  field_simp
  ring

theorem measure (α β c:ℂ)(v u h k:X→ℂ)(iv:Integrable v μ)(iu:Integrable u μ)(ih:Integrable h μ)(ik:Integrable k μ):
    (∫x,center α β c v u h k x ∂μ)=(∫x,k x ∂μ)-α*(∫x,h x ∂μ)-β*(∫x,u x ∂μ)+(α*β-c)*(∫x,v x ∂μ):=by
  have s1:Integrable (fun x=>k x-α*h x) μ:=ik.sub (ih.const_mul _)
  have s2:Integrable (fun x=>k x-α*h x-β*u x) μ:=s1.sub (iu.const_mul _)
  unfold center
  erw [integral_add s2 (iv.const_mul _),integral_sub s1 (iu.const_mul _),integral_sub ik (ih.const_mul _)]
  simp only [integral_const_mul]

theorem column (f g:X→ℂ)(hf:Integrable f μ)(hg:Integrable g μ):
    HasDerivAt (concert μ f g) (∫x,g x ∂μ) 0:=by
  have eq:concert μ f g=fun t=>(∫x,f x ∂μ)+t*(∫x,g x ∂μ):=by
    funext t
    unfold concert
    rw [integral_add hf (hg.const_mul t),integral_const_mul]
  rw [eq]
  simpa +instances only [id_eq,one_mul] using (((hasDerivAt_id (0:ℂ)).mul_const (∫x,g x ∂μ)).const_add (∫x,f x ∂μ))

theorem original (o a b j v u h k:X→ℂ)(io:Integrable o μ)(ia:Integrable a μ)(ib:Integrable b μ)(ij:Integrable j μ)
    (iv:Integrable v μ)(iu:Integrable u μ)(ih:Integrable h μ)(ik:Integrable k μ)(pos:(∫x,o x ∂μ)≠0):
    let z:=∫x,o x ∂μ
    let α:=(∫x,a x ∂μ)/z
    let β:=(∫x,b x ∂μ)/z
    let c:=(∫x,j x ∂μ)/z-α*β
    HasDerivAt (hearing μ o a b j v u h k) ((∫x,center α β c v u h k x ∂μ)/z) 0:=by
  intro z α β c
  have eq (i l:X→ℂ):concert μ i l 0=(∫x,i x ∂μ):=by simp [concert]
  have p:=WilsonRootedNonflatExponential.pair (column μ o v io iv) (column μ a u ia iu)
    (column μ b h ib ih) (column μ j k ij ik) ((eq o v).trans_ne pos)
  simp only [eq] at p
  rw [measure μ α β c v u h k iv iu ih ik]
  exact (window (a:=∫x,a x ∂μ) (b:=∫x,b x ∂μ) (j:=∫x,j x ∂μ) (v:=∫x,v x ∂μ)
    (u:=∫x,u x ∂μ) (h:=∫x,h x ∂μ) (k:=∫x,k x ∂μ) pos) ▸ p

end YM.Integration.WilsonRootedUnnormalizedHearing
