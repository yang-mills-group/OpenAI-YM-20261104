import YM.MS.Lifting.Letters
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Physical
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Curls
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Fac
/-!
# Marking language

Mixed grades of dressed Wilson marks come from ordinary gauge-link functionals.
To compare marks use a *single* real-color lift of derivative letters in every grade.
These just specify outputs of the free linearized equation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Koszul Real Plane Momentum Wire Tensor Book
open Local Local.BV Local.Physical Landau Color Detect Detect.Mark Submodule
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{f:Grade G}{m:FourP→ℂ} {v b:ℤ}
def inc (x:Axis)(q:FourP):ℂ := I*(q x:ℂ)
def deriv (l:List Axis)(q:FourP):= (l.map (inc · q)).prod
lemma der_nil (q:FourP): deriv [] q=1:=rfl
lemma der_add (a:Axis)(l:List Axis)(q:FourP): deriv (a::l) q=inc a q * deriv l q:=rfl
lemma inc_form (x:Axis): Plane.Shape (inc x) 1:= by unfold inc; simpa [Pi.smul_def] using (Local.Shape.scalar_pow 1 (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Axis=>ℝ) x)).scalar I
lemma der_form (l:List Axis): Plane.Shape (deriv l) l.length:= by
   induction l with
   | nil=> exact ⟨contDiff_const, fun h=>by simp at h, fun u p=>by simp [deriv]⟩
   | cons a l ih=> convert! (inc_form a).mul ih using 1; simp; omega
lemma der_star (l:List Axis)(p:FourP): star (deriv l (-p))=deriv l p:= by
   induction l with
   | nil=> simp [deriv]
   | cons a l ih=> rw [der_add,star_mul',ih, der_add]; simp [inc]

def loose (x:Branch G Axis) : (FourP→ℂ) →ₗ[ℂ] Grade G where
   toFun m i:= if i.1=x then m i.2 else 0
   map_add' f g:= by ext; simp [ite_add_zero] -- names
   map_smul' x f:= by ext; simp
lemma loose_ok (a:Branch G Axis){v:ℤ} (H:Plane.Shape m (v-mslug a)): loose a m∈yields v (ghostNo a):= by
   refine seedStar.mpr ⟨fun i=>?_,fun i h=>?_⟩ -- typo
   · by_cases he:i=a; · subst i; simpa [loose] using H
     simp only [loose, LinearMap.coe_mk, AddHom.coe_mk, he,↓reduceIte]; exact form_zero _
   exact if_neg (fun he=> h (congr_arg ghostNo he))

-- expose `(shape v)` = span polynomial derivatives with imaginary i
def entr (v:ℤ): Submodule ℂ (FourP→ℂ):= Submodule.span ℂ {r|∃ a:List Axis, (a.length:ℤ)=v ∧ r=deriv a}
lemma rise (L: Tensor.T FourP ℂ b.toNat) (p:FourP): Tensor.diagonal L p=∑ f:Fin b.toNat → Axis, (↑(∏ i,p (f i)):ℂ)*L (spike∘f):= by
   let M:=L.toMultilinearMap
   have hm : L (fun _ : Fin b.toNat=>p)= M (fun _ : Fin b.toNat=>∑ t:Axis,p t • spike t):=by simp [M,slam]
   unfold Tensor.diagonal; rw [hm,M.map_sum]; refine Finset.sum_congr rfl fun f _=>?_ ; simp only [M.map_smul_univ]; exact Complex.real_smul ..
lemma display (H:Plane.Shape m v): m∈ entr v:= by
   rcases lt_or_ge v 0 with h|h; · rw [H.charge h]; exact Submodule.zero_mem _
   let Iw (μ:Fin v.toNat→Axis) : FourP→ℂ:= fun p=>↑(∏ i,p (μ i))
   have Hw (u:Fin v.toNat→Axis) : I^v.toNat • Iw u= deriv (List.ofFn u):= by ext p; simp [deriv,Iw,List.prod_ofFn,Function.comp_def,inc,Finset.prod_mul_distrib]
   let L:=Tensor.coeff m v.toNat 0
   have HL:m=Tensor.diagonal L := by apply Plane.Shape.form (by simpa [h] using H) -- h use le
   have he:m=∑ f:Fin v.toNat→Axis, L (spike∘f) • Iw f:= by nth_rw 1 [HL]; ext p; rw [rise,Finset.sum_apply]; exact Finset.sum_congr rfl fun a _=> mul_comm ..
   rw [he]; exact sum_mem fun i _=> smul_mem _ _ (by rw [← inv_smul_smul₀ (pow_ne_zero v.toNat Complex.I_ne_zero) (Iw i),Hw]; exact smul_mem _ _ (Submodule.subset_span (mem_setOf.mpr ⟨_,by simp only [List.length_ofFn]; omega,rfl⟩)))

structure Letter where
   face : Atom Axis
   jets : List Axis
namespace Letter
variable (L:Letter)
def mark (c:CI G): Grade G := loose (L.face,c) (deriv L.jets)
def charge : ℤ:= ghostChannel L.face
def value : ℤ:= dim L.face
-- add length later
def edge : ℤ:= L.value + L.jets.length-L.charge
lemma good (c: CI G): L.mark c∈ yields L.edge L.charge:= by
    change loose (L.face,c) _∈ yields L.edge (ghostNo (L.face,c)); apply loose_ok; convert der_form L.jets using 1; simp only [edge,value,charge,mslug,wfield,ghostNo]; omega
lemma cloak (c: CI G): over (L.mark c)=L.mark c:= by ext i; by_cases hc:i.1=(L.face,c) <;> simp [painted,invert, mark,loose,hc,der_star]
lemma weight (u:G.El)(c:CI G): advance u (L.mark c)=∑ x:CI G, wc u x c • L.mark x:= by
   ext ⟨⟨a,k⟩,q⟩; by_cases h:a=L.face <;> simp [advance,mark,loose,h,setLeg]
end Letter

def Loose (v b:ℤ) := {f:Grade G|∃ (a:Letter) (c:CI G), a.edge=v ∧ a.charge=b ∧ f=a.mark c}
lemma includeL (H:f∈ yields v b) : f∈span ℂ (Loose v b):= by
   let O (x:Branch G Axis): FourP→ℂ := fun q=> f (x,q); let T:=span ℂ (Loose (G:=G) v b)
   have hp:f = ∑ x:Branch G Axis, loose x (O x):= by ext ⟨i,q⟩; simp [loose,O]
   have he x : loose x (O x)∈ T:= by
       by_cases hv:ghostNo x=b; swap; · rw [show O x=0 from funext fun q=> (seedStar.mp H).real' _ hv,map_zero]; exact T.zero_mem
       have ht : entr (v-mslug x) ≤ Submodule.comap (loose x) T:= by
          rw [entr,span_le]; rintro k ⟨a,ha,rfl⟩; exact subset_span (mem_setOf.mpr ⟨⟨x.1,a⟩,x.2,show (dim x.1:ℤ)+a.length-ghostChannel x.1=v by unfold mslug ghostNo wfield at ha; omega,hv,rfl⟩)
       exact ht (display ((seedStar.mp H).form x))
   rw [hp]; exact sum_mem fun i _=> he i

-- physical lifting seeds; gauge oriented square uses ordered arbitrary pair, incl zero curls.
namespace Plaq
variable (D:Plaq) (i:CI G)
def mark : Grade G:= gpath D.i D.j i (deriv D.jets)
def value : ℤ:= 2+D.jets.length
lemma horiz : Horizontal (D.mark i) D.value:= gps D.i D.j i _ (show Plane.Shape (deriv D.jets) _ by convert der_form _ using 1; unfold value; omega)
lemma cloak : over (D.mark i)=D.mark i:= by
   ext ⟨⟨⟨_|a,_|_⟩,k⟩,q⟩ <;> simp only [painted,mark,invert,gpath,apply_ite star,star_zero,star_sub,star_mul',star_one,der_star]; simp
lemma weight (u:G.El) : advance u (D.mark i)=∑ x:CI G, wc u x i • D.mark x:= by
   ext ⟨⟨⟨_|a,_|_⟩,k⟩,q⟩ <;> simp [advance,gpath,mark]
end Plaq
def Paths (v b:ℤ) := {f:Grade G|∃ (a:Plaq) (c:CI G), a.value=v ∧ b=0 ∧ f=a.mark c}
def gMap (a b:Axis)(i:CI G): (FourP→ℂ) →ₗ[ℂ] Grade G where
    toFun m:= gpath a b i m
    map_add' f g:= by ext ⟨⟨⟨_|x,_|_⟩,k⟩,q⟩ <;> simp [gpath,add_mul,ite_add_zero]
    map_smul' r f:= by ext ⟨⟨⟨_|x,_|_⟩,k⟩,q⟩ <;> simp [gpath,mul_assoc]
lemma includeP (H: Horizontal f v): f∈ span ℂ (Paths v 0):= by
   let T:=span ℂ (Paths (G:=G) v 0); have he (a b:Axis)(i:CI G) : entr (v-2)≤ Submodule.comap (gMap a b i) T:= by
       rw [entr,span_le]; rintro f ⟨u,hu,rfl⟩; exact subset_span (mem_setOf.mpr ⟨⟨a,b,u⟩,i,show 2+(u.length:ℤ)=v by omega,rfl,rfl⟩)
   refine span_le.mpr ?_ (oriented H); rintro x ⟨u,w,i,f,h,rfl⟩; exact he u w i (display h)
end YM.MS.Lifting
