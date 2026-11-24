import YM.Integration.WilsonRetainedSignedStencilTaylor

/-! The real coefficient expansion on the actual finite Wilson label frame. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedSignedStencilBasis
open Function Finset Lattice Wilson Source Labels Dict06.Wil PhysicalNext.Repeat.Legato
open WilsonRetainedStencilMass (Index basis)
open WilsonRetainedStencilTaylor (Fragment)
open WilsonRetainedSignedStencilTaylor
open private linear from YM.Integration.WilsonRetainedStencilMass
open scoped BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

def weight (φ:Reading)(c:ℂ)(b:Bool):ℂ:=if b then read φ (c*Complex.I) else read φ c

private theorem split (φ:Reading)(c z:ℂ):
    read φ (c*z)=∑b:Bool,weight φ c b*read (part b) z:=by
  have placed:c*z=z.re • c+z.im • (c*Complex.I):=by
    rw [Complex.real_smul,Complex.real_smul]
    conv_lhs=>rw [←Complex.re_add_im z]
    ring
  rw [placed,map_add,map_smul,map_smul]
  simp only [Fintype.sum_bool,weight,part,Bool.false_eq_true,if_false,if_true,Complex.real_smul]
  change (z.re:ℂ)*read φ c+(z.im:ℂ)*read φ (c*Complex.I)=
      read φ (c*Complex.I)*(z.im:ℂ)+read φ c*(z.re:ℂ)
  ring

theorem bounded (φ:Reading)(cap:∀z,|φ z|≤‖z‖)(c:ℂ)(b:Bool):‖weight φ c b‖≤‖c‖:=by
  cases b
  · exact (show ‖weight φ c false‖=|φ c| from (Complex.norm_real _).trans (Real.norm_eq_abs _)).trans_le (cap c)
  · calc ‖weight φ c true‖=|φ (c*Complex.I)|:=(Complex.norm_real _).trans (Real.norm_eq_abs _)
         _≤‖c*Complex.I‖:=cap _
         _=‖c‖:=by simp

def coefficient (φ:I→Reading)(y:∀i,R.family.label (d i))(a:Index R d)(s:I→Bool):ℂ:=
  ∏i,weight (φ i) (y i (a i)) (s i)

theorem expanded (φ:I→Reading)(y:∀i,R.family.label (d i))(x:Fragment R d):
    material R d φ y x=
      ∑a:Index R d,∑s:I→Bool,coefficient R d φ y a s*material R d (part ∘ s) (WilsonRetainedStencilMass.basis R d a) x:=by
  have row (i:I):read (φ i) (echo (R.family.localSection (d i)) (y i) (x i))=
      ∑k,∑b:Bool,weight (φ i) (y i k) b*
        read (part b) (echo (R.family.localSection (d i)) (Pi.single k 1) (x i)):=by
    rw [linear (R.family.localSection (d i)) (y i) (x i),map_sum]
    exact sum_congr rfl (fun k _=>split (φ i) _ _)
  unfold material
  rw [prod_congr rfl (fun i _=>row i),Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  rw [Fintype.prod_sum]
  exact sum_congr rfl (fun s _=>prod_mul_distrib)

theorem charge (φ:I→Reading)(cap:∀i z,|φ i z|≤‖z‖)(θ:ℝ)(y:∀i,R.family.label (d i))
    (a:Index R d)(s:I→Bool):
    ‖coefficient R d φ (fun i=>(R.family.labels.level (d i)).scaled θ⁻¹ (y i)) a s‖≤
      ‖WilsonCoherentReportingFrame.charge R d θ y a‖:=by
  unfold coefficient WilsonCoherentReportingFrame.charge
  rw [norm_prod,norm_prod]
  exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>bounded (φ i) (cap i) _ (s i))

end YM.Integration.WilsonRetainedSignedStencilBasis
