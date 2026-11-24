import YM.Integration.WilsonCoherentFrozenPrice

/-! The physical chart can retain an arbitrary compact pivot on each
participating edge. Repeated pivot values remain coupled. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentPivotStencil
open Function Lattice Wilson RG Finset
open RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [Fintype I] (J : I → Lamp G)
local notation "L" => Slice J

def field (b : L → G.El) (z : L → G.Color) : ℂ :=
  exhibit J (fun j => G.lieExp (z j)*b j)

def row (b : L → G.El) (z : L → G.Color) (p : ℕ) (g : ℝ) : ℂ :=
  ∑ j ∈ range (p+1),g^j • SignedChartTaylor.jet (field J b) z j

theorem extension : ∃ F : ((L → G.Mat) × (L → G.Color)) → ℂ,
    ContDiff ℝ ω F ∧ ∀ (b : L → G.El) (z : L → G.Color),
      F (fun j => G.mat (b j),z) = field J b z := by
  obtain ⟨F,hF,rep⟩ := WilsonCoherentFrozenStencil.original J ∅
  let act := fun v : (L → G.Mat) × (L → G.Color) =>
    ((fun j => G.mat (G.lieExp (v.2 j))*v.1 j), (0 : L → G.Color))
  have hot : ContDiff ℝ ω act :=
    (contDiff_pi.mpr fun j => (G.exp_jet.comp ((contDiff_apply ℝ G.Color j).comp contDiff_snd)).mul
      ((contDiff_apply ℝ G.Mat j).comp contDiff_fst)).prodMk contDiff_const
  refine ⟨F ∘ act,hF.comp hot,?_⟩
  intro b z
  let u : L → G.El := fun j => G.lieExp (z j)*b j
  have empty : WilsonCoherentFrozenStencil.field J ∅ u 0 = u := by
    funext j
    simp [WilsonCoherentFrozenStencil.field]
  have h := rep u 0
  rw [WilsonCoherentFrozenStencil.mark,empty] at h
  simpa only [Function.comp_apply,act,u,G.mat_mul,field] using h

theorem purchased (p : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ (n : Side) (o : I → Site n)
    (U : Config G n) (b : L → G.El) (z : L → G.Color) (t : ℝ),
    0<t → t*‖z‖<1 →
    (∀ j, U (legs J o j)=G.lieExp (t • z j)*b j) →
    ‖tally J o U-row J b z p t‖ ≤ C*(t*‖z‖)^(p+1) := by
  obtain ⟨F,hF,rep⟩ := extension J
  let base := fun b : L → G.El => ((fun j => G.mat (b j)),(0 : L → G.Color))
  have hb : Continuous base := (continuous_pi fun j=>G.continuous_mat.comp (continuous_apply j)).prodMk continuous_const
  obtain ⟨C,hC,bill⟩ := WilsonCoherentFrozenTaylor.purchased F hF base hb p
  refine ⟨C,hC,?_⟩
  intro n o U b z t ht inside hit
  let a := ((0 : L → G.Mat),z)
  have size : ‖a‖=‖z‖ := by simp [a,Prod.norm_def]
  have eq (u : ℝ) : F (base b+u•a) = field J b (u•z) := by simpa [base,a] using rep b (u•z)
  have actual : field J b (t•z)=tally J o U := by
    rw [field,←exhibition J o U]
    exact congrArg (exhibit J) (funext fun j => (hit j).symm)
  have h := bill b a t ht (size ▸ inside)
  rw [size,eq,actual] at h
  simpa only [SignedChartTaylor.jet,eq,row] using h

end YM.Integration.WilsonCoherentPivotStencil
