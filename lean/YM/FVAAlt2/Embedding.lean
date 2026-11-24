import YM.FVAAlt2.Land
import YM.FVAAlt2.LatticeFourier

/-! Embed the actual three (one real + a Grassmann pair) sets of integration variables in
all four kinds of MS mode slots before evaluating the super Wick map. -/
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.FVAAlt2
open Lattice Finset Pert.Orb PertExtension GaussianScore SchemeRG11.Sway Function
open MS MS.Native MS.Koszul MS.Cylinder MS.Plane MS.Landau

variable {G:Gauge}{n:Side}
local notation "X" => Land G n
local notation "U" => ScalarGhost G n

-- Use Sum type to simplify finite sums
abbrev Alpha (ι κ:Type) := ι ⊕ (κ ⊕ κ)
variable {ι κ:Type}
@[match_pattern] abbrev avec(i:ι):Alpha ι κ:=.inl i
@[match_pattern] abbrev gh(i:κ):Alpha ι κ:=.inr (.inl i)
@[match_pattern] abbrev antigh(i:κ):Alpha ι κ:=.inr (.inr i)
abbrev isOdd : Sector (Alpha ι κ) := Sum.elim (fun _=>false) (fun _=>true)

def fields (a:X)(c b:U) : Mode G n → ℝ
 | (((some i,false),k),x)=> a.val.val (x,i) k
 | (((none,false),k),x)=> c.val x k
 | (((some i,true),k),x)=> (gM b).val (x,i) k
 | (_,_)=> 0

lemma fields_true (a a':X)(c b c' b':U)(hf:fields a c b=fields a' c' b') : a=a' ∧ c=c' ∧ b=b' := by
  refine ⟨Subtype.ext (Subtype.ext (funext (fun ⟨x,i⟩=>PiLp.ext fun k=>congrFun hf (((some i,false),k),x)))),
    Subtype.ext (funext fun x=> PiLp.ext fun k=>congrFun hf (((none,false),k),x)),?_⟩
  exact mean_inj (congrArg dLin (show gM b=gM b' from Subtype.ext (funext fun ⟨x,i⟩=>PiLp.ext fun k=>congrFun hf (((some i,true),k),x))))

def fieldL (G:Gauge)(n:Side): Land G n × (ScalarGhost G n × ScalarGhost G n) →ₗ[ℝ] (Mode G n→ℝ) := {
  toFun x:=fields x.1 x.2.1 x.2.2
  map_add' x y:=by
    funext ⟨⟨⟨i,b⟩,k⟩,z⟩; change fields (x.1+_) (x.2.1+_) (x.2.2+_) _=_+_
    cases i <;> cases b <;> simp only [fields,map_add, Pi.add_apply, Submodule.coe_add, PiLp.add_apply,zero_add]
  map_smul' r x:=by
    funext ⟨⟨⟨i,b⟩,k⟩,z⟩; change fields (r•_) (r•_) (r•_) _=r•_
    cases i <;> cases b <;> simp only [fields, map_smul, Pi.smul_apply, Submodule.coe_smul_of_tower, PiLp.smul_apply,smul_zero] }
lemma fieldL_apply (a:X)(c b:U): fieldL G n (a,(c,b))=fields a c b:=rfl
lemma fieldL_injective (n:Side)(G:Gauge): Injective (fieldL G n):=fun _ _ hab=>
    let ⟨x,y,z⟩:=fields_true _ _ _ _ _ _ hab
    Prod.ext x (Prod.ext y z)

variable [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A: Module.Basis ι ℝ (Land G n))(b: Module.Basis κ ℝ (ScalarGhost G n))

def coordBasis : Module.Basis (Alpha ι κ) ℝ (X × (U × U)) := A.prod (b.prod (barBasis b)) -- letter order! no operator/dress

def embeddingℝ : Matrix (Alpha ι κ) (Mode G n) ℝ:= fun i=>fieldL G n (coordBasis A b i)

def embeddingM : Matrix (Alpha ι κ) (Mode G n) ℂ := (embeddingℝ A b).map Complex.ofReal

lemma embAℝ (i : ι) : embeddingℝ A b (avec i)=fields (A i) 0 0 := by
  unfold embeddingℝ coordBasis fieldL avec; simp
lemma embGℝ (i : κ) : embeddingℝ A b (gh i)=fields 0 (b i) 0 := by
  unfold embeddingℝ coordBasis fieldL gh; simp
lemma embKℝ (i : κ) : embeddingℝ A b (antigh i)=fields 0 0 (barBasis b i) := by
  unfold embeddingℝ coordBasis fieldL antigh; simp
lemma embA (i : ι) (x : Mode G n): embeddingM A b (avec i) x=fields (A i) 0 0 x := by unfold embeddingM; rw [Matrix.map_apply, embAℝ]
lemma embG (i : κ)(x): embeddingM A b (gh i) x=fields 0 (b i) 0 x := by unfold embeddingM; rw [Matrix.map_apply, embGℝ]
lemma embK (i : κ)(x): embeddingM A b (antigh i) x=fields 0 0 (barBasis b i) x := by unfold embeddingM; rw [Matrix.map_apply, embKℝ]

lemma embTie : Tie Draft.DotFlip isOdd (embeddingM A b):=by
  rintro ⟨⟨⟨_|x,_|_⟩,_⟩,_⟩ (i|i|i) he
  all_goals first | rfl | (exfalso; apply he; first | rw [embA A b i]| rw [embG A b i]| rw [embK A b i])
  all_goals simp [fields]

lemma embLap (f : Alpha ι κ → ℝ) :
    (embeddingℝ A b).transpose.mulVec f=fieldL G n ((coordBasis A b).equivFun.symm f) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum]; funext x; simp_rw [Finset.sum_apply,map_smul]
  unfold Matrix.mulVec dotProduct
  exact Finset.sum_congr rfl fun i _=> mul_comm _ _

lemma embInj : Function.Injective (embeddingℝ A b).transpose.mulVec:= by
  intro x y he; rw [embLap,embLap] at he; exact (coordBasis A b).equivFun.symm.injective ((fieldL_injective ..) he) -- order

lemma emb_real (x:Alpha ι κ→ℂ): Complex.re ∘ ((embeddingM A b).transpose.mulVec x) = (embeddingℝ A b).transpose.mulVec (Complex.re ∘ x) := by funext i; simp [embeddingM,Matrix.mulVec,dotProduct,Complex.re_sum]
lemma emb_imag (x:Alpha ι κ→ℂ): Complex.im ∘ ((embeddingM A b).transpose.mulVec x) = (embeddingℝ A b).transpose.mulVec (Complex.im ∘ x) := by funext i; simp [embeddingM,Matrix.mulVec,dotProduct,Complex.im_sum]

lemma embInjC : Function.Injective (embeddingM A b).transpose.mulVec:= by
  intro x y he; funext i; exact Complex.ext (congrFun (embInj A b (((emb_real A b x).symm.trans <| (congrArg (Complex.re ∘ ·) he).trans (emb_real A b y)))) i) (congrFun (embInj A b ((emb_imag A b x).symm.trans <| (congrArg (Complex.im ∘ ·) he).trans (emb_imag A b y))) i)
end YM.FVAAlt2
