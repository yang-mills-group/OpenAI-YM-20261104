import YM.AveragedStep.Formal.Reals
/- Free Key covariance and translation of Wick rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD.TreeHeat
open Filter Function Lattice RG Wilson Precision Tree Set
open scoped Topology BigOperators Classical Matrix
open Push.Uniform Matrix MvPolynomial
variable {c f:Side}{G:Gauge}{S:StepData c f}(F:Forest S.ratio)(A:ChartRatio G)
-- general notation
variable {I:Type*}[Fintype I]

def plank (x : I→ℝ):Pol I:=∑ i, MvPolynomial.C (x i)*X i
def translate (V:Cabin G c→ℝ)(i: Key F G):ℝ:=∑ j:Cabin G c,bracken S A F i j * V j
/-- solve to cancel classical shift. H and B responses have PLUS sign in action. -/
def route (x:Cabin G c→ℝ):Key F G→ℝ:= (body A F)⁻¹ *ᵥ (- translate F A x)
lemma settles (h:IsUnit (body A F).det)(x:Cabin G c→ℝ)(i:Key F G):(∑ j,body A F i j * route F A x j)+translate F A x i=0:=by
 let B:=translate F A x
 change (body A F *ᵥ route F A x) i + B i=0
 rw [route,mulVec_mulVec,mul_nonsing_inv _ h, one_mulVec]; exact neg_add_cancel _
-- symmetric T from WP3a, don't assume isunit directly from h branches at all sides.
def stone (h:S.patch.Branches S.kernel G): Frost (Key F G) where
 cov := ((body A F)⁻¹: Matrix (Key F G) _ ℝ)
 swap := by
   intro i j
   have he:(body A F).IsHermitian:=balanced F h (Classical.choice inferInstance) A
   have hh: ((body A F)⁻¹).IsHermitian := he.inv
   have hh': (body A F)⁻¹ j i=(body A F)⁻¹ i j := by simpa using (congrFun (congrFun hh i) j)
   exact hh'.symm

lemma shine_plank (h:S.patch.Branches S.kernel G)(he:IsUnit (body A F).det)(x:Cabin G c→ℝ)(p:Pol (Key F G))(i:Key F G):
    let T:=shine (stone F A h) (route F A x)
    T ((plank (body A F i) + MvPolynomial.C (translate F A x i))*p)=T (glide i p):=by
 intro T
 let H:=body A F; let Q(j):=T (glide j p)
 have ht(a:ℝ)(u:Pol (Key F G)): T (MvPolynomial.C a * u)=a*T u := by rw [C_mul',_root_.map_smul]; rfl
 rw [add_mul,plank,Finset.sum_mul,_root_.map_add,_root_.map_sum,ht]; simp_rw [mul_assoc,ht]
 have hx(j): T (X j * p)= route F A x j*T p+ ∑ k,H⁻¹ j k * Q k:= shine_wick ..
 simp only [hx,mul_add,Finset.sum_add_distrib]
 simp_rw [Finset.mul_sum,← mul_assoc]; rw [← Finset.sum_mul,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)]; -- sum_comm may matched mean? after ←sum_mul, contains mean nested? body entries opaque.
 simp_rw [←Finset.sum_mul]
 have hw(k):∑ j, body A F i j * (H⁻¹) j k = (1:Matrix (Key F G) (Key F G) ℝ) i k:=by
    rw [←mul_apply]; rw [show body A F=H from rfl,mul_nonsing_inv _ he]
 simp only [hw,one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true] -- i=k maybe sum_ite
 have hf:=settles F A he x i
 unfold Q; linear_combination T p * hf

def place (x:Cabin G c→ℝ): Ink G c f→Pol (Key F G) := fun i=>i.1.elim (fun e=>if h:e∈ F.trunks then 0 else X (⟨e,h⟩,i.2)) (fun j=>MvPolynomial.C (x (j,i.2)))
def grid (x:Cabin G c→ℝ): Pol (Ink G c f)→ₐ[ℝ] Pol (Key F G):= aeval (place F x)
lemma grid_hatch (x:Cabin G c→ℝ)(i:Cabin G c):grid F x (X (hatch i))=MvPolynomial.C (x i):=by rw [grid,aeval_X];rfl
lemma grid_fkey (x:Cabin G c→ℝ)(i:Key F G):grid F x (X (fkey F i))=X i:=by rw [grid,aeval_X]; simp [place,fkey,fieldKey,i.1.property]
lemma grid_pin (x:Cabin G c→ℝ){e:Edge (Site f)}(he:e∈F.trunks)(i:G.ColorIndex): grid F x (X (Sum.inl e,i))=0:= by rw [grid,aeval_X]; simp [place,he]
lemma grid_glide(x:Cabin G c→ℝ)(i:Key F G)(p:Pol (Ink G c f)):grid F x (glide (fkey F i) p)=glide i (grid F x p):=by
 induction p using MvPolynomial.induction_on with
 | C r=> simp [glide,grid]
 | add p q a b=>simp only [_root_.map_add,a,b]
 | mul_X p j a=>
   rw [glide_many,map_mul,_root_.map_add,map_mul,map_mul,glide_many,a,glide_X]
   by_cases he:j=fkey F i; · rw [he,if_pos rfl,grid_fkey,glide_X,if_pos rfl,map_one]
   rw [if_neg he,map_zero,mul_zero]; cases j with | mk y t=>
    obtain e|z:=y
    · by_cases hm:e∈F.trunks; · rw [grid_pin F _ hm t]; simp
      let j':Key F G:=(⟨e,hm⟩,t)
      rw [show (Sum.inl e,t)=fkey F j' from rfl,grid_fkey,glide_X,if_neg (show j'≠i from fun hz=>he (congrArg (fkey F) hz)),mul_zero]
    rw [show (Sum.inr z,t)= hatch (f:=f) (G:=G) (z,t) from rfl,grid_hatch]; simp [glide]
/-- Already a linear functional on complete Ink (coarse V tests allowed). -/
def damper (H:S.patch.Branches S.kernel G)(x:Cabin G c→ℝ):Pol (Ink G c f)→ₗ[ℝ] ℝ:=
    (shine (stone F A H) (route F A x)).comp (grid F x).toLinearMap
lemma damper_one (H:S.patch.Branches S.kernel G)(x:Cabin G c→ℝ):damper F A H x 1=1:=by
 unfold damper; rw [LinearMap.comp_apply]; simp only [AlgHom.toLinearMap_apply,map_one]; exact shine_one ..
def lintel (i:Key F G): Pol (Ink G c f) := ∑ j, C (body A F i j)*X (fkey F j)
def twig (i:Key F G): Pol (Ink G c f) := ∑ j:Cabin G c, C (bracken S A F i j)*X (hatch j)
lemma grid_C (x:Cabin G c→ℝ)(a:ℝ): grid F x (C a)=C a:=by unfold grid; simp
lemma aligns (i:Key F G)(x:Cabin G c→ℝ):grid F x (lintel F A i+twig F A i)=plank (body A F i)+C (translate F A x i):=by
 rw [_root_.map_add]; congr 1
 · unfold lintel plank; simp_rw [_root_.map_sum,map_mul,grid_C,grid_fkey]
 unfold twig translate; simp_rw [_root_.map_sum,map_mul,grid_C,grid_hatch]
lemma damping (i:Key F G)(H:S.patch.Branches S.kernel G)(ht:IsUnit (body A F).det)(x:Cabin G c→ℝ)(p:Pol (Ink G c f)):
    damper F A H x ((lintel F A i+twig F A i)*p) = damper F A H x (glide (fkey F i) p):=by
 change shine _ _ (grid F x _) = shine _ _ (grid F x _); rw [map_mul,aligns,shine_plank F A H ht x (grid F x p) i,grid_glide]
end YM.AveragedStep.SD.TreeHeat
