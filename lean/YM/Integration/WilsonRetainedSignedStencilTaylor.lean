import YM.Integration.WilsonRetainedStencilMass

/-! Independent real quadratures of finitely many original Wilson stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedSignedStencilTaylor
open Function Finset Lattice Wilson Source Labels Dict06.Series Dict06.Wil
open PhysicalNext.Repeat.Legato WilsonRetainedStencilTaylor
open private remainder capped from YM.Integration.WilsonRetainedStencilTaylor
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

abbrev Reading := ℂ→L[ℝ]ℝ

def part (b:Bool):Reading:=if b then Complex.imCLM else Complex.reCLM

theorem contracted (b:Bool)(z:ℂ):|part b z|≤‖z‖:=by
  cases b
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

def read (φ:Reading):ℂ→L[ℝ]ℂ:=Complex.ofRealCLM.comp φ

def material (φ:I→Reading) (y:∀i,R.family.label (d i)) (x:Fragment R d):ℂ:=
  ∏i,read (φ i) (echo (R.family.localSection (d i)) (y i) (x i))

theorem real_product (φ:I→Reading) (y:∀i,R.family.label (d i)) (x:Fragment R d):
    material R d φ y x= ((∏i,φ i (echo (R.family.localSection (d i)) (y i) (x i)):ℝ):ℂ):=by
  simp only [Complex.ofReal_prod]
  rfl

theorem smooth (φ:I→Reading) (y:∀i,R.family.label (d i)):ContDiff ℝ ω (material R d φ y):=by
  unfold material
  generalize (univ:Finset I)=s
  induction s using Finset.induction_on with
  | empty=>simp only [prod_empty];exact contDiff_const
  | insert i s hi ih=>
    simp_rw [prod_insert hi]
    exact ((read (φ i)).contDiff.comp ((echo_smooth (R.family.localSection (d i)) _).comp
      (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun i:I=>Panel (R.family.localSection (d i)).stencil G) i).contDiff)).mul ih

theorem price (s:I→Bool) (y:∀i,R.family.label (d i)) (p:ℕ):
    ∃C:ℝ,0≤C ∧ ∀ a:Fragment R d,∀ t:ℝ,0<t →
      ‖WilsonRetainedStencilMass.error (fun u:ℝ=>material R d (part ∘ s) y (u•a)) p t‖≤
      C*(t*‖a‖)^(p+1):=by
  choose b bound using fun i:I=>capped (R.family.localSection (d i)) (y i)
  apply remainder (material R d (part ∘ s) y) (smooth ..) (∏i,b i) _ p
  intro x
  rw [material,norm_prod]
  apply prod_le_prod (fun _ _=>norm_nonneg _)
  intro i _
  exact ((Complex.norm_real _).trans_le ((contracted (s i) _).trans (bound i (x i))))

end YM.Integration.WilsonRetainedSignedStencilTaylor
