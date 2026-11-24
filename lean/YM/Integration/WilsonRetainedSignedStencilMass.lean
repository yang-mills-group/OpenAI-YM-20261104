import YM.Integration.WilsonRetainedSignedStencilBasis

/-! One scaled coefficient tariff for all independently selected real readings. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedSignedStencilMass
open Function Finset Lattice Wilson Source Labels Dict06.Series PhysicalNext.Repeat.Legato
open WilsonRetainedStencilMass (Index basis error)
open WilsonRetainedStencilTaylor (Fragment)
open WilsonRetainedSignedStencilTaylor WilsonRetainedSignedStencilBasis
open private error_sum from YM.Integration.WilsonRetainedStencilMass
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius NNReal
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

theorem purchased (p:ℕ):∃C:ℝ,0≤C ∧ ∀φ:I→Reading,(∀i z,|φ i z|≤‖z‖) →
    ∀θ:ℝ,∀y:∀i,R.family.label (d i),∀a:Fragment R d,∀t:ℝ,0<t →
    let l:=fun i=>(R.family.labels.level (d i)).scaled θ⁻¹ (y i)
    ‖error (fun u:ℝ=>material R d φ l (u•a)) p t‖≤
      WilsonCoherentReportingPivot.mass R d θ y*(C*(t*‖a‖)^(p+1)):=by
  let Marks:=Index R d × (I→Bool)
  choose fee nonneg bought using fun v:Marks=>price R d v.2 (WilsonRetainedStencilMass.basis R d v.1) p
  let costs (v:Marks):ℝ≥0:=⟨fee v,nonneg v⟩
  let top:ℝ:=(univ.sup costs:ℝ≥0)
  let count:ℝ:=Fintype.card (I→Bool)
  refine ⟨count*top,mul_nonneg (Nat.cast_nonneg _) (univ.sup costs).property,?_⟩
  intro φ cap θ y a t ht l
  let f (v:Marks) (u:ℝ):=material R d (part ∘ v.2) (WilsonRetainedStencilMass.basis R d v.1) (u•a)
  let c (v:Marks):=coefficient R d φ l v.1 v.2
  let h:=(t*‖a‖)^(p+1)
  have h0:0≤h:=pow_nonneg (mul_nonneg ht.le (norm_nonneg _)) _
  have expand:(fun u:ℝ=>material R d φ l (u•a))=(fun u=>∑v:Marks,c v*f v u):=by
    funext u
    rw [Fintype.sum_prod_type]
    exact expanded R d φ l _
  have sm (v:Marks):ContDiffAt ℝ ω (f v) 0:=
    ((smooth R d (part ∘ v.2) (WilsonRetainedStencilMass.basis R d v.1)).comp (contDiff_id.smul contDiff_const)).contDiffAt
  rw [expand,error_sum f c sm]
  calc ‖∑v:Marks,c v*error (f v) p t‖≤∑v:Marks,‖c v*error (f v) p t‖:=norm_sum_le _ _
       _≤∑v:Marks,‖WilsonCoherentReportingFrame.charge R d θ y v.1‖*(top*h):=by
         apply sum_le_sum
         intro v _
         have upper:fee v≤top:=le_sup (f:=costs) (mem_univ v)
         rw [norm_mul]
         exact mul_le_mul (WilsonRetainedSignedStencilBasis.charge R d φ cap θ y v.1 v.2)
           ((bought v a t ht).trans (mul_le_mul_of_nonneg_right upper h0)) (norm_nonneg _) (norm_nonneg _)
       _=WilsonCoherentReportingPivot.mass R d θ y*((count*top)*h):=by
         rw [Fintype.sum_prod_type]
         simp only [sum_const,card_univ,nsmul_eq_mul]
         unfold WilsonCoherentReportingPivot.mass count
         rw [sum_mul]
         apply sum_congr rfl
         intro i _
         ring

end YM.Integration.WilsonRetainedSignedStencilMass
