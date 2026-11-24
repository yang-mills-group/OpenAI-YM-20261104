import YM.Integration.WilsonSeparatedOriginalMarkedCubic

/-! Positive conditional copies of a common spatial test at a fixed old field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalReplicaMeasure
open RG05Readout RG05Readout.Address
open MeasureTheory Finset Set RG Lattice Wilson Source Extraction Push.GridApprox
open PhysicalNext.Repeat.Legato RG05Readout.Records WilsonSeparatedOriginalMarkedCubic
open scoped BigOperators Classical Topology
variable {A:Type*}[MeasurableSpace A]

def read (μ:Measure A)(H:(Fin 3 → A)→ℂ):ℂ:=
  (∫a,H ![a,a,a] ∂μ) - ((∫a,∫b,H ![a,a,b] ∂μ ∂μ)+(∫a,∫b,H ![a,b,a] ∂μ ∂μ)+
    (∫a,∫b,H ![b,a,a] ∂μ ∂μ)) + 2*(∫a,∫b,∫c,H ![a,b,c] ∂μ ∂μ ∂μ)

private theorem middle (μ:Measure A)(f:Fin 3 → A→ℂ):
    (∫a,∫b,(f 0 a*f 1 b)*f 2 a ∂μ ∂μ)=(∫a,f 0 a*f 2 a ∂μ)*(∫b,f 1 b ∂μ):=by
  simp_rw [show ∀a b,(f 0 a*f 1 b)*f 2 a=(f 0 a*f 2 a)*f 1 b from fun a b=>by ring,
    integral_const_mul,integral_mul_const]

private theorem other (μ:Measure A)(f:Fin 3 → A→ℂ):
    (∫a,∫b,(f 0 b*f 1 a)*f 2 a ∂μ ∂μ)=(∫a,f 1 a*f 2 a ∂μ)*(∫b,f 0 b ∂μ):=by
  simp_rw [show ∀a b,(f 0 b*f 1 a)*f 2 a=(f 1 a*f 2 a)*f 0 b from fun a b=>by ring,
    integral_const_mul,integral_mul_const]

private theorem independent (μ:Measure A)(f:Fin 3 → A→ℂ):
    (∫a,∫b,∫c,(f 0 a*f 1 b)*f 2 c ∂μ ∂μ ∂μ)=(∫a,f 0 a ∂μ)*(∫b,f 1 b ∂μ)*(∫c,f 2 c ∂μ):=by
  simp_rw [integral_const_mul,integral_mul_const,integral_const_mul,integral_mul_const]

theorem grouped (μ:Measure A)(f:Fin 3 → A→ℂ):
    read μ (fun U=>∏i:Fin 3,f i (U i))=cubic (fun s=>∫W,∏i∈s,f i W ∂μ):=by
  unfold read cubic
  simp only [Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  have tail (a b:A):Matrix.vecHead (Matrix.vecTail ![a,b])=b:=rfl
  simp_rw [tail]
  simp_rw [middle μ f,other μ f,independent μ f]
  simp [integral_const_mul,integral_mul_const]

end YM.Integration.WilsonSeparatedOriginalReplicaMeasure
